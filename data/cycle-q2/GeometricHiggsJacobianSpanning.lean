import Proposal.GeometricHiggsJacobianFrames
import Proposal.GeometricHiggsJacobianMembership

/-!
# Spanning the genuine graded Jacobian quotient on the Fermat open

In each degree and character the unit frame determinant expresses every
homogeneous polynomial as a combination of the standard monomials and
the actual partial-derivative multiples. Passing to the quotient by the
Jacobian ideal removes the latter columns.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HiggsJacobianFrames

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2GenericSexticGradient (CoeffRing universalF seedEvaluation)
open CycleQ2FermatJacobian (cutoff)
open CycleQ2HiggsJacobianMembership (partial_homogeneous)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

theorem cutoff_weight (i : Fin 5) :
    Finsupp.weight fullGrading (Finsupp.single i (cutoff i)) =
      (6 - (fullGrading i).1, -(fullGrading i).2) := by
  rw [Finsupp.weight_single]
  fin_cases i <;> decide

theorem mapped_column_homogeneous {n : ℕ} {χ : ZMod 3} (e : Index n χ) :
    HG (MvPolynomial.map φ (column e)) (n, χ) := by
  classical
  unfold column
  split_ifs with h
  · rw [map_monomial]
    exact isWeightedHomogeneous_monomial fullGrading _ _ e.property
  · simp only [map_mul, map_monomial, ← pderiv_map]
    let i := pivot h
    let a := exp e - Finsupp.single i (cutoff i)
    have hg : Finsupp.weight fullGrading a + (6 - (fullGrading i).1, -(fullGrading i).2) =
        (n,χ) := by
      rw [← cutoff_weight, ← map_add, tsub_add_cancel_of_le (pivot_le h)]
      exact e.property
    rw [← hg]
    exact (isWeightedHomogeneous_monomial fullGrading a _ rfl).mul (partial_homogeneous φ i)

theorem exists_column_expansion {n : ℕ} {χ : ZMod 3} (hd : IsUnit (φ (frameDet n χ)))
    (p : MvPolynomial (Fin 5) R) (hp : HG p (n,χ)) :
    ∃ c : Index n χ → R, ∑ j, c j • MvPolynomial.map φ (column j) = p := by
  classical
  let A := (frameMatrix n χ).map φ
  have hA : IsUnit A.det := by
    rw [frameDet, RingHom.map_det] at hd
    exact hd
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    (A.isUnit_iff_isUnit_det.mpr hA)) (fun j => p.coeff (exp j))
  refine ⟨c, ?_⟩
  let r := ∑ j, c j • MvPolynomial.map φ (column j)
  have hr : HG r (n,χ) := (weightedHomogeneousSubmodule R fullGrading (n,χ)).sum_mem
    fun j _ => (weightedHomogeneousSubmodule R fullGrading (n,χ)).smul_mem _ (mapped_column_homogeneous φ j)
  apply MvPolynomial.ext
  intro v
  by_cases hv : Finsupp.weight fullGrading v = (n,χ)
  · obtain ⟨e, rfl⟩ := exists_index v hv
    simpa only [A, Matrix.mulVec, dotProduct, frameMatrix, Matrix.map_apply, coeff_sum,
      coeff_smul, smul_eq_mul, coeff_map, mul_comm] using congrFun hc e
  · have zero {t : MvPolynomial (Fin 5) R} (ht : HG t (n,χ)) : coeff v t = 0 := by
      by_contra h
      exact hv (ht h)
    exact (zero hr).trans (zero hp).symm

abbrev QuotientRing := MvPolynomial (Fin 5) R ⧸ jacobian φ

def quotientMap : MvPolynomial (Fin 5) R →ₐ[R] QuotientRing φ := Ideal.Quotient.mkₐ R _

def gradedPiece (n : ℕ) (χ : ZMod 3) : Submodule R (QuotientRing φ) :=
  (weightedHomogeneousSubmodule R fullGrading (n,χ)).map (quotientMap φ).toLinearMap

def boundedClass {n : ℕ} {χ : ZMod 3} (e : Bounded n χ) : QuotientRing φ :=
  quotientMap φ (monomial (exp e.val) 1)

/-- The quotient submodule is defined by the bigrading of actual polynomials.
The nonvanishing frame determinant makes its standard monomials span. -/
theorem gradedPiece_eq_span {n : ℕ} {χ : ZMod 3} (hd : IsUnit (φ (frameDet n χ))) :
    gradedPiece φ n χ = Submodule.span R (Set.range (boundedClass φ (n := n) (χ := χ))) := by
  classical
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨c,hc⟩ := exists_column_expansion φ hd p hp
    change quotientMap φ p ∈ _
    rw [← hc, map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_smul]
    apply Submodule.smul_mem
    by_cases hj : Standard j
    · have he : quotientMap φ (MvPolynomial.map φ (column j)) = boundedClass φ ⟨j,hj⟩ := by
        simp [column, hj, boundedClass]
      rw [he]
      exact Submodule.subset_span (Set.mem_range_self _)
    · have hz : quotientMap φ (MvPolynomial.map φ (column j)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (nonstandard_column_mem φ hj)
      rw [hz]
      exact zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨e,rfl⟩
    exact ⟨monomial (exp e.val) 1,
      isWeightedHomogeneous_monomial fullGrading _ _ e.val.property, rfl⟩

end CycleQ2HiggsJacobianFrames
end

#print axioms CycleQ2HiggsJacobianFrames.gradedPiece_eq_span
