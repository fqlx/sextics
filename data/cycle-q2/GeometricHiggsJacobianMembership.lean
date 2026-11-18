import Proposal.SolutionSupport02Part02
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Degree and character in the Jacobian ideal of the invariant sextic

On every coefficient specialization, project an arbitrary ideal-membership
witness onto the unique multiplier bidegree that can contribute to the
given component. A partial derivative of weight greater than the target
weight contributes zero.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2HiggsJacobianMembership

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2GenericSexticGradient

variable {K : Type*} [CommRing K]

theorem partial_homogeneous (φ : CoeffRing →+* K) (i : Fin 5) :
    HG (pderiv i (MvPolynomial.map φ universalF))
      (6 - (fullGrading i).1, -(fullGrading i).2) := by
  have hF : HG (MvPolynomial.map φ universalF) (6, 0) := by
    rw [universalF, map_fullInvariantPolynomial]
    exact fullInvariantPolynomial_homogeneous _ _
  apply hF.pderiv
  apply Prod.ext
  · have hi : (fullGrading i).1 ≤ 6 := by fin_cases i <;> decide
    exact Nat.sub_add_cancel hi
  · exact neg_add_cancel _

private def multiplier (N : ℕ) (χ : ZMod 3) (e : ℕ) (κ : ZMod 3) (u : Poly K) :
    Poly K :=
  if e ≤ N then weightedHomogeneousComponent fullGrading (N - e, χ - κ) u else 0

private theorem multiplier_homogeneous (N : ℕ) (χ : ZMod 3) (e : ℕ) (κ : ZMod 3)
    (u : Poly K) : HG (multiplier N χ e κ u) (N - e, χ - κ) := by
  unfold multiplier
  split
  · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · exact (weightedHomogeneousSubmodule K fullGrading _).zero_mem

private theorem component_mul_below (N : ℕ) (χ : ZMod 3) (e : ℕ) (κ : ZMod 3)
    (u q : Poly K) (hq : HG q (e, κ)) (h : N < e) :
    weightedHomogeneousComponent fullGrading (N, χ) (u * q) = 0 := by
  induction u using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : HG (monomial a c : Poly K) (Finsupp.weight fullGrading a) :=
      isWeightedHomogeneous_monomial fullGrading a c rfl
    apply (hm.mul hq).weightedHomogeneousComponent_ne
    intro heq
    have hd := congrArg Prod.fst heq
    change N = (Finsupp.weight fullGrading a).1 + e at hd
    omega
  | add a b ha hb =>
    rw [add_mul, map_add, ha, hb, add_zero]

private theorem component_mul (N : ℕ) (χ : ZMod 3) (e : ℕ) (κ : ZMod 3)
    (u q : Poly K) (hq : HG q (e, κ)) :
    weightedHomogeneousComponent fullGrading (N, χ) (u * q) =
      multiplier N χ e κ u * q := by
  by_cases h : e ≤ N
  · have hgrade : (N - e, χ - κ) + (e, κ) = (N, χ) :=
      Prod.ext (Nat.sub_add_cancel h) (sub_add_cancel _ _)
    simpa only [multiplier, if_pos h, hgrade] using
      CycleQ2WeightedComponent.component_mul fullGrading u q (N - e, χ - κ) (e, κ) hq
  · rw [component_mul_below N χ e κ u q hq (Nat.lt_of_not_ge h), multiplier, if_neg h, zero_mul]

/-- Project an arbitrary Jacobian ideal representation onto one bidegree. -/
theorem component_multipliers (φ : CoeffRing →+* K) (N : ℕ) (χ : ZMod 3)
    (p : Poly K)
    (hmem : p ∈ Ideal.span (Set.range (fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF)))) :
    ∃ h : Fin 5 → Poly K,
      (∀ i, HG (h i) (N - (6 - (fullGrading i).1), χ + (fullGrading i).2)) ∧
      (∀ i, N < 6 - (fullGrading i).1 → h i = 0) ∧
      weightedHomogeneousComponent fullGrading (N, χ) p =
        ∑ i, h i * pderiv i (MvPolynomial.map φ universalF) := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  refine ⟨fun i => multiplier N χ (6 - (fullGrading i).1) (-(fullGrading i).2) (u i),
    fun i => ?_, fun i hi => ?_, ?_⟩
  · simpa only [sub_neg_eq_add] using multiplier_homogeneous N χ
      (6 - (fullGrading i).1) (-(fullGrading i).2) (u i)
  · exact if_neg (Nat.not_le_of_lt hi)
  · have hproj := congrArg (weightedHomogeneousComponent fullGrading (N, χ)) hu
    rw [map_sum] at hproj
    exact hproj.symm.trans (Finset.sum_congr rfl (fun i _ =>
      component_mul N χ _ _ (u i) _ (partial_homogeneous φ i)))

theorem component_mem (φ : CoeffRing →+* K) (N : ℕ) (χ : ZMod 3) {p : Poly K}
    (hmem : p ∈ Ideal.span (Set.range (fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF)))) :
    weightedHomogeneousComponent fullGrading (N, χ) p ∈
      Ideal.span (Set.range (fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF))) := by
  obtain ⟨h, _, _, heq⟩ := component_multipliers φ N χ p hmem
  exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨h, heq.symm⟩

/-- The Jacobian multipliers have their prescribed degree and character.
Every partial of weight above the target can be omitted entirely. -/
theorem membership_iff (φ : CoeffRing →+* K) (N : ℕ) (χ : ZMod 3)
    (p : Poly K) (hp : HG p (N, χ)) :
    p ∈ Ideal.span (Set.range (fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF))) ↔
      ∃ h : Fin 5 → Poly K,
        (∀ i, HG (h i) (N - (6 - (fullGrading i).1), χ + (fullGrading i).2)) ∧
        (∀ i, N < 6 - (fullGrading i).1 → h i = 0) ∧
        p = ∑ i, h i * pderiv i (MvPolynomial.map φ universalF) := by
  constructor
  · intro hmem
    simpa only [hp.weightedHomogeneousComponent_same] using component_multipliers φ N χ p hmem
  · rintro ⟨h, _, _, hsum⟩
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨h, hsum.symm⟩

end CycleQ2HiggsJacobianMembership
end

#print axioms CycleQ2HiggsJacobianMembership.membership_iff
