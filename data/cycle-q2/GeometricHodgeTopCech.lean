import Proposal.GeometricHodgeTwistCech

/-!
# The top Laurent Čech quotient of the monic sextic

On the four weight-one opens, a monomial extends to an omitted-coordinate
face exactly when its exponent in that coordinate is nonnegative. The
only degree-zero term with four negative exponents is
`w² / (x₀ x₁ x₂ x₃)`. Taking its coefficient identifies the top
ordered Čech quotient with the coefficient group.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeTopCech

open CycleQ2HodgeTwistCech

variable {A : Type*} [AddCommGroup A] {t : ℤ}

abbrev TopSection (A : Type*) [AddCommGroup A] (t : ℤ) := sections A t Finset.univ
abbrev Faces (A : Type*) [AddCommGroup A] (t : ℤ) :=
  (i : Vertex) → sections A t (Finset.univ.erase i)

private def signAt (i : Vertex) (a : A) : A := if Even i.val then a else -a

/-- The alternating differential evaluated on the ordered fourfold intersection. -/
def boundary (c : Faces A t) : TopSection A t :=
  ∑ i, if Even i.val then restrict (Finset.subset_univ _) (c i)
       else -restrict (Finset.subset_univ _) (c i)

private theorem boundary_coeff (c : Faces A t) (j : Fin 3) (e : Exp) :
    (boundary c).val j e = ∑ i, signAt i ((c i).val j e) := by
  classical
  let value : TopSection A t →+ A :=
    { toFun := fun p => p.val j e, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change value (∑ i : Vertex, if Even i.val then restrict (Finset.subset_univ _) (c i)
            else -restrict (Finset.subset_univ _) (c i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Even i.val <;> simp [h, value, signAt, restrict] <;> rfl

private def index (e : Exp) : Vertex :=
  if h : ∃ i, 0 ≤ e i then Classical.choose h else 0

private def facePart (p : TopSection A t) (i : Vertex) : sections A t (Finset.univ.erase i) := by
  classical
  refine ⟨fun j => (p.val j).filter (fun e => (∃ k, 0 ≤ e k) ∧ index e = i), ?_⟩
  intro j e h
  rw [Finsupp.filter_apply]
  split_ifs with he
  · apply p.property j e
    intro hp
    apply h
    refine ⟨hp.1, fun k hk => Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    rintro rfl
    have hn : 0 ≤ e (index e) := by
      simpa only [index, dif_pos he.1] using Classical.choose_spec he.1
    exact (not_lt_of_ge (he.2 ▸ hn)) hk
  · rfl

private def primitive (p : TopSection A t) (i : Vertex) : sections A t (Finset.univ.erase i) :=
  if Even i.val then facePart p i else -facePart p i

/-- The kernel of projection onto the all-negative monomials is the image
of the alternating sum of the four triple-intersection restrictions. -/
theorem boundary_iff (p : TopSection A t) :
    (∃ c : Faces A t, boundary c = p) ↔
      ∀ (j : Fin 3) (e : Exp), (∀ i, e i < 0) → p.val j e = 0 := by
  classical
  constructor
  · rintro ⟨c, rfl⟩ j e h
    rw [boundary_coeff]
    apply Finset.sum_eq_zero
    intro i _
    have hz := (c i).property j e (fun he => (Finset.notMem_erase i _ (he.2 i (h i))))
    simp [hz, signAt]
  · intro hp
    refine ⟨primitive p, Subtype.ext ?_⟩
    funext j
    ext e
    rw [boundary_coeff]
    have hterm (i : Vertex) : signAt i (((primitive p i).val j) e) =
        if (∃ k, 0 ≤ e k) ∧ index e = i then p.val j e else 0 := by
      by_cases h : Even i.val <;> simp [h, signAt, primitive, facePart, Finsupp.filter_apply]
    simp_rw [hterm]
    by_cases he : ∃ k, 0 ≤ e k
    · simp [he]
    · simpa [he] using (hp j e (fun i => lt_of_not_ge (fun hn => he ⟨i, hn⟩))).symm

private theorem only_top_weight (j : Fin 3) (e : Exp)
    (hw : (∑ i, e i) + 2 * (j.val : ℤ) = 0) (hn : ∀ i, e i < 0) :
    j = 2 ∧ e = fun _ => -1 := by
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  rw [Fin.sum_univ_four] at hw
  have hv : (j.val : ℤ) = 2 := by
    have := j.isLt
    omega
  have hj : j = 2 := Fin.ext (by change j.val = 2; exact_mod_cast hv)
  refine ⟨hj, ?_⟩
  subst j
  norm_num at hw
  funext i
  fin_cases i <;> dsimp <;> omega

/-- Coefficient of the unique top Laurent monomial in degree zero. -/
def trace : TopSection A 0 →+ A where
  toFun p := p.val 2 (fun _ => -1)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem trace_eq_zero_iff (p : TopSection A 0) :
    trace p = 0 ↔ ∃ c : Faces A 0, boundary c = p := by
  rw [boundary_iff]
  constructor
  · intro h j e hn
    by_cases hw : (∑ i, e i) + 2 * (j.val : ℤ) = 0
    · obtain ⟨rfl,rfl⟩ := only_top_weight j e hw hn
      exact h
    · exact p.property j e (fun he => hw he.1)
  · exact fun h => h 2 (fun _ => -1) (fun _ => by decide)

def representative (a : A) : TopSection A 0 := by
  classical
  refine ⟨fun j => if j = 2 then Finsupp.single (fun _ => -1) a else 0, ?_⟩
  intro j e hn
  by_cases hj : j = 2
  · subst j
    simp only [if_true, Finsupp.single_apply]
    split_ifs with he
    · subst e
      exact False.elim (hn ⟨by norm_num, fun i _ => Finset.mem_univ i⟩)
    · rfl
  · simp [hj]

@[simp] theorem trace_representative (a : A) : trace (representative a) = a := by
  change (if (2 : Fin 3) = 2 then Finsupp.single (fun _ : Vertex => (-1 : ℤ)) a else 0)
      (fun _ => -1) = a
  simp

/-- Complementary Laurent exponent for the monomial in the normalized trace. -/
def dualExponent (e : Exp) : Exp := fun i => -1 - e i

theorem dualExponent_twice (e : Exp) : dualExponent (dualExponent e) = e := by
  funext i
  dsimp [dualExponent]
  omega

theorem dual_degree (j : Fin 3) (e : Exp) :
    (∑ i, dualExponent e i) + 2 * (j.rev.val : ℤ) = -((∑ i, e i) + 2 * (j.val : ℤ)) := by
  have hj : (j.rev.val : ℤ) + j.val = 2 := by fin_cases j <;> decide
  simp only [Fin.sum_univ_four, dualExponent]
  omega

/-- The surviving top monomials at twist t are indexed by the global monomials
of twist -t through the two complementary power-basis slots and Laurent degrees. -/
theorem dual_global_iff (k : ℤ) (j : Fin 3) (e : Exp) :
    Allowed (-k) ∅ j.rev (dualExponent e) ↔
      Allowed k Finset.univ j e ∧ ∀ i, e i < 0 := by
  constructor
  · rintro ⟨hw,hp⟩
    rw [dual_degree] at hw
    refine ⟨⟨by omega, fun i _ => Finset.mem_univ i⟩, fun i => ?_⟩
    have h : ¬ dualExponent e i < 0 := fun hn => Finset.notMem_empty i (hp i hn)
    dsimp [dualExponent] at h
    omega
  · rintro ⟨⟨hw,_⟩, hn⟩
    refine ⟨by rw [dual_degree, hw], fun i hi => ?_⟩
    dsimp [dualExponent] at hi
    have h := hn i
    omega

end CycleQ2HodgeTopCech

#print axioms CycleQ2HodgeTopCech.trace_eq_zero_iff
#print axioms CycleQ2HodgeTopCech.trace_representative
