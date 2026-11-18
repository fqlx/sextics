import Proposal.ScratchWeightedDoublePoleCech

/-! Weighted Euler degrees of the actual simplex numerators and corrections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedPoleEuler
open CycleQ2WeightedDoublePoleCech
variable {ι k K : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] [Field K] [Algebra k K]

def HasWeight (E : Derivation k K K) (n : ℤ) (a : K) : Prop := E a = (n : K)*a

variable {E : Derivation k K K}
theorem zero_weight (n : ℤ) : HasWeight E n 0 := by simp [HasWeight]
theorem same_weight {n : ℤ} {a b : K} (ha : HasWeight E n a) (hb : HasWeight E n b) :
    HasWeight E n (a-b) := by
  change E (a-b) = _
  rw [map_sub,ha,hb,mul_sub]
theorem add_weight {n : ℤ} {a b : K} (ha : HasWeight E n a) (hb : HasWeight E n b) :
    HasWeight E n (a+b) := by
  change E (a+b) = _
  rw [map_add,ha,hb,mul_add]
theorem neg_weight {n : ℤ} {a : K} (ha : HasWeight E n a) : HasWeight E n (-a) := by
  change E (-a) = _
  rw [map_neg,ha,mul_neg]
theorem mul_weight {n m : ℤ} {a b : K} (ha : HasWeight E n a) (hb : HasWeight E m b) :
    HasWeight E (n+m) (a*b) := by
  change E (a*b) = _
  rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,ha,hb,Int.cast_add]
  ring
theorem div_weight {n m : ℤ} {a b : K} (ha : HasWeight E n a) (hb : HasWeight E m b) :
    HasWeight E (n-m) (a/b) := by
  change E (a/b) = _
  by_cases h : b=0
  · simp [h]
  rw [Derivation.leibniz_div,smul_eq_mul,smul_eq_mul,smul_eq_mul,ha,hb,Int.cast_sub]
  field_simp [h] <;> ring

variable (D : ι → Derivation k K K) (w : ι → ℤ)
def EulerCommutes (E : Derivation k K K) : Prop :=
  ∀ i x, E (D i x) = D i (E x) - (w i : K) * D i x

theorem partial_weight (hE : EulerCommutes D w E) {n : ℤ} {a : K} (ha : HasWeight E n a) (i : ι) :
    HasWeight E (n-w i) (D i a) := by
  change E (D i a) = _
  rw [hE,ha,Derivation.leibniz,Derivation.map_intCast,smul_zero,add_zero,smul_eq_mul,Int.cast_sub]
  ring

variable {F B : K} {d b : ℤ} (hE : EulerCommutes D w E) (hF : HasWeight E d F) (hB : HasWeight E b B)

theorem coeff_weight (i : ι) : HasWeight E (b-d+w i) (coeff D F B i) := by
  convert div_weight hB (partial_weight D w hE hF i) using 1 <;> ring

theorem lie_weight (i : ι) : HasWeight E (b-d) (lie D F B i) := by
  convert partial_weight D w hE (coeff_weight D w hE hF hB i) i using 1 <;> ring

theorem twice_weight (i : ι) : HasWeight E (b-2*d+w i) (twiceCoeff D F B i) := by
  convert div_weight (lie_weight D w hE hF hB i) (partial_weight D w hE hF i) using 1 <;> ring

theorem pair_weight (i j : ι) : HasWeight E (b-2*d+w i+w j) (pairCoeff D F B i j) := by
  convert div_weight hB (mul_weight (partial_weight D w hE hF i) (partial_weight D w hE hF j))
    using 1 <;> ring

theorem vertex_weight (i : ι) : HasWeight E (b-3*d) (vertex D F B i) := by
  convert div_weight (partial_weight D w hE (twice_weight D w hE hF hB i) i) hF using 1 <;> ring

private theorem one_weight (n : ℤ) (i a : ι) {x : K}
    (hx : HasWeight E (n+w i) x) : HasWeight E (n+w a) (oneIndex i x a) := by
  by_cases h : a=i
  · subst a; simpa [oneIndex] using hx
  · simpa [oneIndex,Pi.single_eq_of_ne h] using (zero_weight (E:=E) (n+w a))

private theorem two_weight (n : ℤ) (i j a c : ι) {x : K}
    (hx : HasWeight E (n+w i+w j) x) : HasWeight E (n+w a+w c) (twoIndex i j x a c) := by
  change HasWeight _ _ (Pi.single i (Pi.single j x) a c - Pi.single j (Pi.single i x) a c)
  apply same_weight
  · by_cases h : a=i
    · subst a; simpa [oneIndex] using one_weight w (n+w i) j c hx
    · simpa [Pi.single_eq_of_ne h] using (zero_weight (E:=E) (n+w a+w c))
  · by_cases h : a=j
    · subst a
      have hx' : HasWeight E (n+w j+w i) x := by simpa [add_right_comm] using hx
      simpa [oneIndex] using one_weight w (n+w j) i c hx'
    · simpa [Pi.single_eq_of_ne h] using (zero_weight (E:=E) (n+w a+w c))

theorem edge_weight (i j a : ι) : HasWeight E (b-3*d+w a) (edge D F B i j a) := by
  have h₁ : HasWeight E (b-2*d+w j) (D i (pairCoeff D F B i j)) := by
    convert partial_weight D w hE (pair_weight D w hE hF hB i j) i using 1 <;> ring
  have h₂ : HasWeight E (b-2*d+w i) (D j (pairCoeff D F B i j)) := by
    convert partial_weight D w hE (pair_weight D w hE hF hB i j) j using 1 <;> ring
  change HasWeight _ _ (oneIndex j _ a - oneIndex i _ a)
  apply same_weight
  · apply one_weight w (b-3*d) j a
    convert div_weight (add_weight (twice_weight D w hE hF hB j) h₁) hF using 1 <;> ring
  · apply one_weight w (b-3*d) i a
    convert div_weight (add_weight (twice_weight D w hE hF hB i) h₂) hF using 1 <;> ring

theorem face_weight (i j l a c : ι) : HasWeight E (b-3*d+w a+w c) (face D F B i j l a c) := by
  have H (u v : ι) : HasWeight E (b-3*d+w a+w c) (edgeCorrection D F B u v a c) := by
    apply two_weight w (b-3*d) u v a c
    convert div_weight (pair_weight D w hE hF hB u v) hF using 1 <;> ring
  exact same_weight (add_weight (neg_weight (H j l)) (H i l)) (H i j)

/-- The weighted Euler derivation of the ambient rational field. -/
def radial (x : ι → K) : Derivation k K K := ∑ j, ((w j : K)*x j) • D j

theorem radial_apply (x : ι → K) (z : K) :
    radial D w x z = ∑ j, ((w j : K)*x j) * D j z := by
  change Derivation.coeFnAddMonoidHom (∑ j, ((w j : K)*x j) • D j) z = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem radial_commutes (x : ι → K)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hc : ∀ i j u, D i (D j u) = D j (D i u)) :
    EulerCommutes D w (radial D w x) := by
  classical
  intro i u
  simp only [radial_apply,map_sum]
  have h (j : ι) : D i (((w j : K)*x j) * D j u) =
      ((w j : K)*x j)*D j (D i u) + (if j=i then (w i : K)*D i u else 0) := by
    rw [Derivation.leibniz,Derivation.leibniz,Derivation.map_intCast,smul_zero,add_zero]
    simp only [smul_eq_mul,hc i j,hx]
    by_cases h : j=i
    · subst j; simp <;> ring
    · simp [h,Ne.symm h]
  simp_rw [h]
  simp [Finset.sum_add_distrib]

end CycleQ2WeightedPoleEuler
end
#print axioms CycleQ2WeightedPoleEuler.face_weight
