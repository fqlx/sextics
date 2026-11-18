import Proposal.GeometricHodgeTopCech
import Proposal.GeometricHodgeTwistPolynomial

/-!
# The Fermat cubic reduction in the top Laurent trace

A product of three bounded Jacobian monomials, multiplied by one further
w, has w-power at most four. Reducing powers three and four by the
Fermat cubic produces terms only in slots zero and one. Thus only an
original w-power two can pair with the negative exponent in all four
weight-one coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeFermatTraceRows
open CycleQ2HodgeTwistCech CycleQ2HodgeTopCech
open CycleQ2GeometricIncidenceProj (geometricWeight)

variable {A : Type*} [AddCommGroup A]

def term (j : Fin 3) (e : Exp) (c : A) (hd : (∑ i, e i) + 2*(j.val : ℤ) = 0) : TopSection A 0 := by
  classical
  refine ⟨fun k => if k = j then Finsupp.single e c else 0, ?_⟩
  intro k x hn
  by_cases hk : k = j
  · subst k
    simp only [if_pos rfl, Finsupp.single_apply]
    split_ifs with hx
    · subst x; exact False.elim (hn ⟨hd, fun i _ => Finset.mem_univ i⟩)
    · rfl
  · simp [hk]

theorem trace_term (j : Fin 3) (e : Exp) (c : A) (hd) :
    trace (term j e c hd) = (if j = 2 ∧ e = fun _ => (-1 : ℤ) then c else 0) := by
  classical
  change (if (2 : Fin 3) = j then Finsupp.single e c else 0) (fun _ => -1) = _
  by_cases hj : j = 2 <;> by_cases he : e = fun _ => (-1 : ℤ) <;> simp [hj,he,eq_comm,Finsupp.single_apply]

abbrev Degree (d : Fin 5 →₀ ℕ) := Finsupp.weight geometricWeight d = 18

def shift (d : Fin 5 →₀ ℕ) : Exp := fun a => (d a.castSucc : ℤ) - 5

def power (d : Fin 5 →₀ ℕ) : ℕ := 1 + d (Fin.last 4)

private theorem weight_formula (d : Fin 5 →₀ ℕ) :
    Finsupp.weight geometricWeight d = (∑ a : Fin 4, d a.castSucc) + 2 * d (Fin.last 4) := by
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_castSucc]
  simp only [CycleQ2SeedFermatProj.geometricWeight_castSucc, show geometricWeight (Fin.last 4) = 2 from rfl,
    smul_eq_mul, mul_one, Nat.mul_comm]

theorem shift_degree (d : Fin 5 →₀ ℕ) (hd : Degree d) :
    (∑ a, shift d a) + 2 * (power d : ℤ) = 0 := by
  have hw := ((weight_formula d).symm.trans hd)
  have hw' : (∑ a : Fin 4, (d a.castSucc : ℤ)) + 2 * (d (Fin.last 4) : ℤ) = 18 := by exact_mod_cast hw
  simp only [shift, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    power, Nat.cast_add, Nat.cast_one]
  omega

def plusSix (e : Exp) (a : Vertex) : Exp := fun k => e k + if k = a then 6 else 0

theorem plusSix_sum (e : Exp) (a : Vertex) : (∑ k, plusSix e a k) = (∑ k, e k) + 6 := by
  classical
  simp [plusSix, Finset.sum_add_distrib]

def normalForm (d : Fin 5 →₀ ℕ) (hd : Degree d) (hm : power d ≤ 4) (c : A) : TopSection A 0 :=
  if h : power d < 3 then term ⟨power d,h⟩ (shift d) c (shift_degree d hd)
  else -∑ a, term ⟨power d - 3, by omega⟩ (plusSix (shift d) a) c (by
    rw [plusSix_sum]
    have := shift_degree d hd
    change (∑ k, shift d k) + 6 + 2 * ((power d - 3 : ℕ) : ℤ) = 0
    rw [Nat.cast_sub (by omega : 3 ≤ power d)]
    omega)

private theorem socle_iff (d : Fin 5 →₀ ℕ) :
    power d = 2 ∧ shift d = (fun _ => (-1 : ℤ)) ↔
      d = CycleQ2FermatJacobian.exponent CycleQ2FermatHiggs.socle := by
  constructor
  · rintro ⟨hw,h⟩
    ext i
    induction i using Fin.lastCases with
    | last => change d (Fin.last 4) = 1; unfold power at hw; omega
    | cast i =>
      have h₁ := congrFun h i
      change (d i.castSucc : ℤ)-5 = -1 at h₁
      have h₂ : CycleQ2FermatJacobian.exponent CycleQ2FermatHiggs.socle i.castSucc = 4 := by
        fin_cases i <;> rfl
      rw [h₂]; omega
  · rintro rfl
    exact ⟨rfl, funext (fun a => by fin_cases a <;> rfl)⟩

theorem trace_normalForm (d : Fin 5 →₀ ℕ) (hd : Degree d) (hm : power d ≤ 4) (c : A) :
    trace (normalForm d hd hm c) = if d = CycleQ2FermatJacobian.exponent CycleQ2FermatHiggs.socle then c else 0 := by
  classical
  rw [← socle_iff]
  by_cases h : power d < 3
  · have hj : (⟨power d,h⟩ : Fin 3) = 2 ↔ power d = 2 := Fin.ext_iff
    simp only [normalForm, dif_pos h, trace_term, hj]
  · rw [normalForm, dif_neg h, map_neg, map_sum]
    have hj : (⟨power d - 3, by omega⟩ : Fin 3) ≠ 2 := by
      intro he
      have he' : power d - 3 = 2 := congrArg Fin.val he
      omega
    have hn : power d ≠ 2 := by omega
    simp [trace_term, hj, hn]

end CycleQ2HodgeFermatTraceRows
end

#print axioms CycleQ2HodgeFermatTraceRows.trace_normalForm
