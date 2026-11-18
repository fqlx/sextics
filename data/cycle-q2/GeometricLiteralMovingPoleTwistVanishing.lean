import Proposal.GeometricLiteralMovingPoleCoefficientGluing
import Proposal.GeometricLiteralMovingPoleTwistedCoordinates
import Proposal.GeometricClosedComponentsCohomology

/-!
# First cohomology of the moving pole forms

The positive pole quotient is the product of the direct images of the fifth
twist on the three translated curves. The identification compares actual
pole coefficients with evaluation of the twist-valued conormal functionals
on each component. The fifth twist has zero first cohomology on the curve,
and the seventh twist has zero first cohomology on the surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingPoleTwistVanishing
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralMovingPoleComponents CycleQ2LiteralMovingPoleCoefficientGluing
  CycleQ2LiteralMovingPoleQuotient CycleQ2LiteralMovingPoleNormalEvaluation
  CycleQ2LiteralTwistedConormalDual CycleQ2LiteralCurvePositiveTwist
  CycleQ2GeometricModuleLocalIso CycleQ2ClosedEmbeddingSheafExact
  CycleQ2LiteralMovingResiduePole CycleQ2ClosedComponentsCohomology
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra

private abbrev normalSheaf (a : Fin 3) : CurveSheaf := addSheaf (normal a)

private theorem avoids (W : ComponentPatch) (a : Fin 3) (h : W.survivor = some a) :
    AvoidsOtherComponents W.toFramedAffine a := by
  intro b hba
  apply W.avoids b
  intro hb
  exact hba (Option.some.inj (hb.symm.trans h))

/-- The frame is evaluation on the orbit pivot followed by the seventh-twist coordinate. -/
private def normalCoefficients : ComponentCoefficients normalSheaf where
  equiv W a hs := coefficient a W.toFramedAffine W.vertices W.within (avoids W a hs) W.carrier le_rfl
  restrict W V a hw hv h s := coefficient_restrict_change a W.toFramedAffine V.toFramedAffine
    W.vertices V.vertices W.within V.within (avoids W a hw) (avoids V a hv) h s

private def normalFive (a : Fin 3) : normalSheaf a ≅ curveTwist 5 :=
  (SheafOfModules.toSheaf C.ringCatSheaf).mapIso (twistedNormalIso (z a) (rootValues_cube complexRoot complexRoot_quadratic a))

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- The actual positive pole quotient is the product of the three pushed-forward fifth twists. -/
def poleFiveIso : poleQuotient t ht ≅ ∏ᶜ (factor (fun _ => curveTwist 5)) :=
  poleCoefficientGluingIso normalCoefficients t ht ≪≫
    Pi.mapIso (fun a => (push (curveComponent a).base).mapIso (normalFive a))

local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : TopCat.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf X) := HasExt.standard _
local instance (X : TopCat.{0}) : HasExt.{1} (X.Sheaf AddCommGrpCat.{0}) := HasExt.standard _

theorem poleQuotientHOne : Subsingleton ((poleQuotient t ht).H' 1 ⊤) := by
  let e := componentHEquiv (fun a => (curveComponent a).base)
    (fun a => (curveComponent a).isClosedEmbedding) (fun _ => curveTwist 5) (poleFiveIso t ht) 1
  exact ⟨fun x y => e.injective (funext fun _ => (positiveTwistHOne_subsingleton 5 (by decide)).elim _ _)⟩

/-- The pole forms of the literal regular moving curve have vanishing first cohomology. -/
theorem poleHOne : Subsingleton ((addSheaf (PoleForms t)).H' 1 ⊤) :=
  poleHOne_subsingleton t ht (poleQuotientHOne t ht)

end CycleQ2LiteralMovingPoleTwistVanishing
end

#print axioms CycleQ2LiteralMovingPoleTwistVanishing.poleFiveIso
#print axioms CycleQ2LiteralMovingPoleTwistVanishing.poleQuotientHOne
#print axioms CycleQ2LiteralMovingPoleTwistVanishing.poleHOne
