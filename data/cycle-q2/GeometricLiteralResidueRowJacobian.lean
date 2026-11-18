import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricLiteralAbelJacobiSeedLiftPoints
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Completing a section-row minor to the augmented surface Jacobian

A nonzero three-column minor makes the two surface differentials and the
section differential linearly independent at the given field-valued point.
A coordinate differential completes these rows to a basis. Its polynomial
determinant maps to the augmented Jacobian on the surface chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueRowJacobian

open MvPolynomial Matrix CycleQ2GeometricSurfaceAdjunction
open CycleQ2LiteralAbelJacobiSeedLiftPoints

private abbrev coord := _root_.finSuccEquiv 3

/-- The polynomial whose image is the augmented determinant in the surface ring. -/
def rowDet (f : Fin 4 → SurfacePoly) : SurfacePoly :=
  (Matrix.of fun i j => pderiv (coord j) (f i)).det

theorem augmentedJacobian_eq (v : Fin 2 → SurfacePoly) (n a : SurfacePoly) :
    augmentedJacobian v n a =
      Ideal.Quotient.mk (surfaceChartIdeal v) (rowDet (augmentedPolynomialRows v n a)) := by
  rw [augmentedJacobian_polynomial, rowDet, RingHom.map_det]
  rfl

private theorem exists_extra_coordinate {K : Type*} [Field K]
    (A : Matrix (Fin 3) (Fin 4) K) (q : Fin 3 → Fin 4)
    (hq : (A.submatrix id q).det ≠ 0) :
    ∃ j : Fin 4, LinearIndependent K
      (Fin.snoc (α := fun _ => Fin 4 → K) A.row (Pi.single j 1)) := by
  let L : (Fin 4 → K) →ₗ[K] (Fin 3 → K) :=
    LinearMap.pi (fun j => LinearMap.proj (q j))
  have hrow : LinearIndependent K A.row := by
    apply LinearIndependent.of_comp L
    exact Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hq))
  let W := Submodule.span K (Set.range A.row)
  have hW : W ≠ ⊤ := by
    intro h
    have hf := finrank_span_eq_card hrow
    change Module.finrank K W = Fintype.card (Fin 3) at hf
    rw [h] at hf
    simp at hf
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, Pi.single j (1 : K) ∉ W := by
    by_contra! hall
    apply hW
    apply top_unique
    rw [← (Pi.basisFun K (Fin 4)).span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    change (Pi.basisFun K (Fin 4)) j ∈ W
    rw [Pi.basisFun_apply]
    exact hall j
  exact ⟨j, linearIndependent_finSnoc.mpr ⟨hrow, hj⟩⟩

/-- The complementing coordinate gives a nonzero raw polynomial determinant at the field point. -/
theorem polynomialDet_of_minor {K : Type*} [Field K]
    (φ : SurfacePoly →+* K) (v : Fin 2 → SurfacePoly) (n : SurfacePoly)
    (q : Fin 3 → Option (Fin 3))
    (hq : φ (jacobianMinor (Fin.snoc (α := fun _ => SurfacePoly) v n) q) ≠ 0) :
    ∃ j : Option (Fin 3), φ (rowDet (augmentedPolynomialRows v n (X j))) ≠ 0 := by
  let f := Fin.snoc (α := fun _ => SurfacePoly) v n
  let A : Matrix (Fin 3) (Fin 4) K := fun i j => φ (pderiv (coord j) (f i))
  have hsub : (A.submatrix id (coord.symm ∘ q)).det ≠ 0 := by
    rw [jacobianMinor, RingHom.map_det] at hq
    rw [← Matrix.det_transpose]
    convert hq using 2
    ext i j
    change φ (pderiv (coord (coord.symm (q i))) (f j)) = φ (pderiv (q i) (f j))
    rw [Equiv.apply_symm_apply]
  obtain ⟨j, hj⟩ := exists_extra_coordinate A (coord.symm ∘ q) hsub
  refine ⟨coord j, ?_⟩
  rw [rowDet, RingHom.map_det]
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  convert hj using 1
  funext a b
  refine Fin.lastCases ?_ (fun k => ?_) a
  · change φ (pderiv (coord b) (X (coord j))) =
        Fin.snoc (α := fun _ => Fin 4 → K) A.row (Pi.single j 1) (Fin.last 3) b
    rw [Fin.snoc_last]
    by_cases h : j = b
    · subst b
      simp [pderiv_X]
    · simp [pderiv_X, h, Ne.symm h]
  · fin_cases k <;> rfl

/-- A surviving three-row minor yields an augmented Jacobian patch containing
the same field point. The fourth polynomial is one of the chart coordinates. -/
theorem exists_coordinate_of_minor {K : Type*} [Field K]
    (v : Fin 2 → SurfacePoly) (n : SurfacePoly) (φ : SurfaceChartRing v →+* K)
    (q : Fin 3 → Option (Fin 3))
    (hq : φ (Ideal.Quotient.mk (surfaceChartIdeal v)
      (jacobianMinor (Fin.snoc (α := fun _ => SurfacePoly) v n) q)) ≠ 0) :
    ∃ j : Option (Fin 3), φ (augmentedJacobian v n (X j)) ≠ 0 := by
  obtain ⟨j, hj⟩ := polynomialDet_of_minor (φ.comp (Ideal.Quotient.mk _)) v n q hq
  exact ⟨j, by rwa [augmentedJacobian_eq]⟩

#print axioms polynomialDet_of_minor
#print axioms exists_coordinate_of_minor

end CycleQ2LiteralResidueRowJacobian
