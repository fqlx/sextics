import Proposal.GeometricHodgeTopCech

/-!
# The top Laurent coefficients for every twist

After restricting a representative to its all-negative exponents, reversal
of the cubic slot and complementary exponents identify the surviving
coefficients with the global monomial basis of the opposite twist.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeTwistTopCoefficients

open CycleQ2HodgeTwistCech CycleQ2HodgeTopCech
variable {A : Type} [AddCommGroup A] {k : ℤ}

private def flip : Exp ≃ Exp :=
  ⟨dualExponent, dualExponent, dualExponent_twice, dualExponent_twice⟩

private theorem dual_nonnegative (e : Exp) : (∀ i, 0 ≤ dualExponent e i) ↔ ∀ i, e i < 0 := by
  constructor <;> intro h i <;> have hi := h i <;> dsimp [dualExponent] at * <;> omega

/-- The coefficient of a global exponent is read at its complementary all-negative top exponent. -/
def coefficients : TopSection A k →+ sections A (-k) ∅ where
  toFun p := ⟨fun j => ((p.val j.rev).equivMapDomain flip).filter (fun e => ∀ i, 0 ≤ e i), by
    intro j e he
    rw [Finsupp.filter_apply]
    split_ifs with hn
    · apply p.property j.rev (dualExponent e)
      intro ha
      apply he
      have hneg : ∀ i, dualExponent e i < 0 := by
        intro i
        have hi := hn i
        dsimp [dualExponent]
        omega
      simpa only [Fin.rev_rev, dualExponent_twice] using (dual_global_iff k j.rev _).2 ⟨ha,hneg⟩
    · rfl⟩
  map_zero' := by
    apply Subtype.ext
    funext j
    ext e
    change (((0 : Exp →₀ A).equivMapDomain flip).filter _ e) = 0
    rw [Finsupp.filter_apply]
    split <;> rfl
  map_add' p q := by
    apply Subtype.ext
    funext j
    ext e
    by_cases he : ∀ i, 0 ≤ e i <;> simp [he]

theorem coefficients_apply (p : TopSection A k) (j : Fin 3) (e : Exp) :
    (coefficients p).val j e = if ∀ i, 0 ≤ e i then p.val j.rev (dualExponent e) else 0 := by
  change (((p.val j.rev).equivMapDomain flip).filter _ e) = _
  rw [Finsupp.filter_apply]
  rfl

/-- The all-negative representative of the given complementary coefficients. -/
def representative (v : sections A (-k) ∅) : TopSection A k :=
  ⟨fun j => (v.val j.rev).equivMapDomain flip, by
    intro j e he
    apply v.property j.rev (dualExponent e)
    exact fun h => he ((dual_global_iff k j e).mp h).1⟩

@[simp] theorem coefficients_representative (v : sections A (-k) ∅) :
    coefficients (representative v) = v := by
  apply Subtype.ext
  funext j
  ext e
  rw [coefficients_apply]
  split_ifs with hn
  · change v.val j.rev.rev (dualExponent (dualExponent e)) = _
    rw [Fin.rev_rev, dualExponent_twice]
  · symm
    apply v.property j e
    intro h
    apply hn
    intro i
    exact le_of_not_gt fun hi => Finset.notMem_empty i (h.2 i hi)

theorem coefficients_eq_zero_iff (p : TopSection A k) :
    coefficients p = 0 ↔ ∃ c : Faces A k, boundary c = p := by
  rw [boundary_iff]
  constructor
  · intro h j e hn
    have hz := congrArg (fun x : sections A (-k) ∅ => x.val j.rev (dualExponent e)) h
    rw [coefficients_apply, if_pos ((dual_nonnegative e).2 hn), Fin.rev_rev, dualExponent_twice] at hz
    exact hz
  · intro h
    apply Subtype.ext
    funext j
    ext e
    rw [coefficients_apply]
    split_ifs with hn
    · apply h
      intro i
      have hi := hn i
      dsimp [dualExponent]
      omega
    · rfl

/-- A negative twist has no global polynomial monomial, including in the cubic power-basis slots. -/
theorem negative_global_subsingleton (h : k < 0) : Subsingleton (sections A k ∅) := by
  apply subsingleton_of_forall_eq 0
  intro v
  apply Subtype.ext
  funext j
  ext e
  apply v.property j e
  intro he
  have hx : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ =>
    le_of_not_gt fun hi => Finset.notMem_empty i (he.2 i hi)
  have hj : 0 ≤ (j.val : ℤ) := by positivity
  have hw := he.1
  omega

#print axioms coefficients_eq_zero_iff
#print axioms coefficients_representative
end CycleQ2HodgeTwistTopCoefficients
end
