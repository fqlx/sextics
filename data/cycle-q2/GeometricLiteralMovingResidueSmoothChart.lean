import Proposal.GeometricLiteralMovingResidueSmoothAlgebra
import Proposal.GeometricLiteralMovingResidueAffineCurve
import Proposal.GeometricLiteralMovingResidueAffineNumerators
import Proposal.GeometricAffineOpenOrdinaryDifferentials

/-!
# Local adjunction on a smooth moving curve chart

When the actual equation differential is a member of a surface
cotangent basis, the chart residue map identifies ordinary Kähler
differentials of the hypersurface with the canonical numerator line
modulo its equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingResidueSmoothChart
open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricExteriorSheaf
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralMovingResidueFaces
  CycleQ2SeedSectionDivisorTransitions CycleQ2LiteralMovingResidueAdjunction
  CycleQ2LiteralMovingResidueSmoothAlgebra CycleQ2GeometricDifferentialSheaf
  CycleQ2ExteriorTopBaseChange
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open CycleQ2AffineOpenOrdinaryDifferentials (toSheaf_bijective_of_isAffineOpen)
open scoped Pointwise

local instance surfaceAlg (V : Surface.Opens) : Algebra ℂ (SectionRing Surface.sheaf V) :=
  sectionAlgebra Surface.sheaf globalCoefficient V
local instance canonicalModule (V : Surface.Opens) :
    Module (SectionRing Surface.sheaf V) (CanonicalForms.val.obj (op V)) :=
  (CanonicalForms.val.obj (op V)).isModule

section Algebra
variable {K R M N : Type*} [CommRing K] [CommRing R] [Algebra K R] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N]

private theorem basisAdjunction (e : R) (E : KaehlerDifferential K R ≃ₗ[R] M)
    (b : Module.Basis (Fin 2) R M) (X : (⋀[R]^2 M) ≃ₗ[R] N)
    (hb : E (KaehlerDifferential.D K R e) = b 0)
    (F : KaehlerDifferential K (R ⧸ Ideal.span {e}) →ₗ[R ⧸ Ideal.span {e}]
      (N ⧸ ((Ideal.span {e} : Ideal R) • (⊤ : Submodule R N))))
    (hF : ∀ ω, F (KaehlerDifferential.map K K R (R ⧸ Ideal.span {e}) ω) =
      ((Ideal.span {e} : Ideal R) • (⊤ : Submodule R N)).mkQ
        (X (exteriorPower.ιMulti R 2 ![E (KaehlerDifferential.D K R e), E ω]))) :
    Function.Bijective F := by
  let B := (E.trans b.equivFun).trans (LinearEquiv.finTwoArrow R R)
  let L := X.symm.trans (topCoordinateEquiv b)
  let P := quotientLine e L
  apply (Function.Bijective.of_comp_iff' P.bijective F).mp
  change Function.Bijective (P.toLinearMap.comp F)
  have hd : B (KaehlerDifferential.D K R e) = (1,0) := by
    change (b.repr (E _) 0, b.repr (E _) 1) = (1,0)
    rw [hb, b.repr_self]
    simp
  apply quotientAdjunction_bijective e B
  · intro ω
    change quotientLine e L (F (KaehlerDifferential.map K K R (R ⧸ Ideal.span {e}) ω)) = _
    rw [hF, quotientLine_mk]
    apply congrArg (Ideal.Quotient.mk (Ideal.span {e}))
    change L (X _) = (B (KaehlerDifferential.D K R e)).1 * (B ω).2 -
      (B (KaehlerDifferential.D K R e)).2 * (B ω).1
    rw [hd]
    change topCoordinate b (X.symm (X (exteriorPower.ιMulti R 2
      ![E (KaehlerDifferential.D K R e),E ω]))) = 1 * b.repr (E ω) 1 - 0 * b.repr (E ω) 0
    rw [X.symm_apply_apply, topCoordinate_wedge, hb, Matrix.det_fin_two]
    simp [Module.Basis.toMatrix_apply]
  · change IsCoprime (Ideal.Quotient.mk (Ideal.span {e}) (B (KaehlerDifferential.D K R e)).1)
      (Ideal.Quotient.mk (Ideal.span {e}) (B (KaehlerDifferential.D K R e)).2)
    rw [hd]
    exact ⟨1,0,by simp⟩

end Algebra

/-- On an affine frame where the equation differential is the first
basis vector, the actual conormal wedge is an isomorphism. -/
theorem chartAdjunction_bijective_of_basis {W : Surface.Opens} (t : Fin 3 → ℂ)
    (j : FrameData W) (hW : IsAffineOpen W) (b : Module.Basis (Fin 2) Γ(Surface,W) (OneForms W))
    (hb : b 0 = equationDifferential W (frameEquation t j))
    (hx : Function.Bijective (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W)) :
    Function.Bijective (chartAdjunction t j) := by
  let R := SectionRing Surface.sheaf W
  let b' : Module.Basis (Fin 2) R (OneForms W) := b
  let E := LinearEquiv.ofBijective (toSheaf Surface.sheaf globalCoefficient W)
    (toSheaf_bijective_of_isAffineOpen globalCoefficient W hW)
  let X := LinearEquiv.ofBijective (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W) hx
  exact basisAdjunction (K := ℂ) (R := R) (frameEquation t j) E b' X hb.symm
    (chartAdjunction t j) (chartAdjunction_map t j)

attribute [local instance] AffineFrame.surfaceAlgebra AffineFrame.curveAlgebra

/-- This identifies the ordinary differentials on the actual curve ring
with the sections of the genuine quotient of the pole sheaf. -/
theorem curveAdjunction_bijective_of_basis {W : Surface.Opens} (t : Fin 3 → ℂ)
    (ht : ∀ i, CycleQ2SeedSectionAffineInjective.ChartRegular t i)
    (j : FrameData W) (hW : IsAffineOpen W) (b : Module.Basis (Fin 2) Γ(Surface,W) (OneForms W))
    (hb : b 0 = equationDifferential W (frameEquation t j))
    (hx : Function.Bijective (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W)) :
    Function.Bijective (curveAdjunction hW t ht j) :=
  (CycleQ2LiteralMovingResidueAffineNumerators.numeratorToResidue_bijective t ht j hW).comp
    ((chartAdjunction_bijective_of_basis t j hW b hb hx).comp
      (CycleQ2GeometricAffineOverlap.differentialEquiv
        (AffineFrame.curveQuotientAlgEquiv hW t ht j)).symm.bijective)

end CycleQ2LiteralMovingResidueSmoothChart
end

#print axioms CycleQ2LiteralMovingResidueSmoothChart.chartAdjunction_bijective_of_basis

#print axioms CycleQ2LiteralMovingResidueSmoothChart.curveAdjunction_bijective_of_basis
