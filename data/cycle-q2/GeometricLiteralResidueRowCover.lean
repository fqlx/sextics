import Proposal.GeometricLiteralResidueRowEvaluation
import Proposal.GeometricLiteralResidueRowPoint
import Proposal.GeometricLiteralResidueRowJacobian
import Proposal.GeometricLiteralAbelJacobiSeedLift
import Proposal.GeometricLiteralAbelJacobiBertiniMinor

/-!
# Augmented Jacobian charts cover the literal moving curve

At every point of the original projective curve, the Bertini minor
and the selected matrix pivot give a local equation and a complementary
coordinate on the literal seed surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralResidueRowCover

open MvPolynomial AlgebraicGeometry
open CycleQ2GeometricSurfaceAdjunction CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionInvertible CycleQ2SeedSectionCurveRows CycleQ2SeedSectionSheafCurveBinding
  CycleQ2RelativeCurveChart CycleQ2RelativeConstantSection CycleQ2SpecializedProjectiveCurve
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2LiteralAbelJacobiSeedLift CycleQ2LiteralAbelJacobiSeedLiftPoints
  CycleQ2LiteralAbelJacobiSeedLiftChart CycleQ2LiteralResidueRowPoint
  CycleQ2LiteralResidueRowEvaluation CycleQ2LiteralResidueRowJacobian

attribute [local instance] CycleQ2RelativeCurveChartFiber.seedCurveChartCommRing

private abbrev equations (i : Fin 3) := dehomogenizedEquations 57 1 i.succ
private abbrev row (t : Fin 3 → ℂ) (i a : Fin 3) :=
  dehomogenize i.succ (relativeSectionPolynomial seed t a)

private theorem chartEquations_literal (t : Fin 3 → ℂ) (i : Fin 3)
    (p : CycleQ2SegreCech.Chart) :
    chartEquations seed t i.succ p = Fin.snoc (equations i) (row t i p.1) := by
  unfold chartEquations equations
  rw [CycleQ2IncidenceDehomogenizedChart.dehomogenizedEquations, dehomogenizedEquations,
    literalPointEquationF, literalPointEquationH]
  rfl

/-- The original section's pivot and an adapted differential chart contain
the image of each curve point under its given closed immersion. -/
theorem of_seedMinorCover (t : Fin 3 → ℂ) (h : SeedMinorCover t) :
    ∀ x : specializedCurve seed t, ∃ (i : Fin 3) (p : Fin 3 × Fin 3) (s : SurfacePoly),
      curveToSurface t x ∈ pivotOpen i p ∧
      curveToSurface t x ∈ principalOpen (coordinateAffineChart 57 1 i.succ)
        (augmentedJacobian (equations i) (row t i p.1) s) := by
  intro x
  obtain ⟨i, z, rfl⟩ := exists_literalChart_prime t x
  obtain ⟨p, q, hp, hq⟩ := h i.succ z
  let φ := (algebraMap _ z.asIdeal.ResidueField).comp (curvePolynomialMap t i.succ seed)
  have hq' : φ (jacobianMinor (Fin.snoc (equations i) (row t i p.1)) q) ≠ 0 := by
    rw [← chartEquations_literal t i p]
    exact fun hz => hq (Ideal.algebraMap_residueField_eq_zero.mp hz)
  obtain ⟨j, hj⟩ := polynomialDet_of_minor φ (equations i) (row t i p.1) q hq'
  refine ⟨i, p, X j, (mem_pivotOpen_iff t i z p).mpr hp, ?_⟩
  let b := rowDet (augmentedPolynomialRows (equations i) (row t i p.1) (X j))
  rw [augmentedJacobian_eq]
  change curveToSurface t _ ∈ principalOpen _ (dehomogenizedMap 57 1 i.succ b)
  rw [principalOpen_polynomial, mem_basicOpen_iff]
  rw [← CycleQ2IncidenceDehomogenizedChart.familyCoordinateChartEquiv_symm_mk,
    AlgEquiv.apply_symm_apply]
  exact fun hz => hj (Ideal.algebraMap_residueField_eq_zero.mpr hz)

/-- Algebraically independent section coordinates supply this cover. -/
theorem of_algebraicIndependent (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) :
    ∀ x : specializedCurve seed t, ∃ (i : Fin 3) (p : Fin 3 × Fin 3) (s : SurfacePoly),
      curveToSurface t x ∈ pivotOpen i p ∧
      curveToSurface t x ∈ principalOpen (coordinateAffineChart 57 1 i.succ)
        (augmentedJacobian (equations i) (row t i p.1) s) :=
  of_seedMinorCover t (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht)

end CycleQ2LiteralResidueRowCover
end

#print axioms CycleQ2LiteralResidueRowCover.of_algebraicIndependent
