import Proposal.GeometricLiteralMovingIntrinsicResidue
import Proposal.GeometricLiteralMovingResidueTrace

/-!
# Surjectivity of the adjunction trace on the moving curve

For the retained algebraically independent section vector the quotient
of canonical poles is the direct image of the Kähler one-form sheaf.
Every scalar is the residue of a class on that curve. The kernel consists
exactly of classes lifting to the ambient sheaf of canonical forms with
a pole on the curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingCurveTraceSurjective
open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2ClosedEmbeddingCohomology CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafCurveBinding CycleQ2SeedProjectiveImageCocycle
  CycleQ2LiteralMovingResidueCurve CycleQ2LiteralMovingResidueExact CycleQ2LiteralMovingResidueTrace
  CycleQ2LiteralMovingQuotientTrace CycleQ2LiteralMovingCurveDifferentialNonzero
  CycleQ2LiteralMovingResidueSmooth CycleQ2LiteralCotangentTrace

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (hi : AlgebraicIndependent ℚ t)

def curveFormResidueEquiv : (curveForms t).H' 1 ⊤ ≃+ (residueQuotient t).H' 1 ⊤ := by
  letI := curveResidue_isIso_of_independent t ht hi
  let e := (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 1).mapIso
    (asIso (curveResidue t ht))
  exact (pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1).trans
    (e.app (op ⊤)).addCommGroupIsoToAddEquiv

theorem differentialTrace_eq (x : (curveForms t).H' 1 ⊤) :
    differentialTrace t ht x = residueTrace t ht (curveFormResidueEquiv t ht hi x) := rfl

include hi in
theorem differentialTrace_surjective : Function.Surjective (differentialTrace t ht) := by
  intro c
  obtain ⟨s, hs⟩ := (algebraicTraceEquiv.surjective) c
  obtain ⟨q, hq⟩ := residueConnecting_surjective t ht s
  obtain ⟨x,hx⟩ := (curveFormResidueEquiv t ht hi).surjective q
  refine ⟨x,?_⟩
  rw [differentialTrace_eq t ht hi, hx]
  change algebraicTrace (residueConnecting t ht ⊤ q) = c
  rw [hq]
  exact hs

theorem differentialTrace_kernel_iff (x : (curveForms t).H' 1 ⊤) :
    differentialTrace t ht x = 0 ↔ ∃ y : (residueComplex t).X₂.H' 1 ⊤,
      y.comp (Ext.mk₀ (residueComplex t).g) (add_zero 1) = curveFormResidueEquiv t ht hi x := by
  rw [differentialTrace_eq t ht hi, residueTrace_eq_zero_iff]

/-- Vanishing of the first cohomology of the pole sheaf suffices for
injectivity, by the actual sheaf residue sequence. -/
def differentialTraceEquivOfVanishing (h : Subsingleton ((residueComplex t).X₂.H' 1 ⊤)) :
    (curveForms t).H' 1 ⊤ ≃+ ℂ := by
  refine AddEquiv.ofBijective (differentialTrace t ht) ⟨?_,differentialTrace_surjective t ht hi⟩
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y,hy⟩ := (differentialTrace_kernel_iff t ht hi x).mp hx
  apply (curveFormResidueEquiv t ht hi).injective
  rw [← hy, h.elim y 0, Ext.zero_comp, map_zero]

end CycleQ2LiteralMovingCurveTraceSurjective
end

#print axioms CycleQ2LiteralMovingCurveTraceSurjective.differentialTrace_surjective
#print axioms CycleQ2LiteralMovingCurveTraceSurjective.differentialTraceEquivOfVanishing
