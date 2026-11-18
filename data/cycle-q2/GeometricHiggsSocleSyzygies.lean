import Proposal.GeometricHiggsSocle
import Proposal.GeometricHiggsJacobianMembership

/-!
# Koszul relations for the full degree-eighteen Jacobian matrix

Each repeated Fermat pivot gives a two-generator Koszul relation in the
universal Jacobian ideal. After adding a multiple of its chosen pivot,
the relation has exactly one nonzero coefficient at Fermat. The resulting
square relation matrix has nonzero determinant over the parameter ring.
Its adjugate transfers vanishing of the chosen columns to every Jacobian
column in the same degree and character.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HiggsSocleSyzygies

open MvPolynomial CycleQ2FermatHiggs CycleQ2FermatJacobian CycleQ2GenericSexticGradient
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2HiggsSocle
open Finset
open scoped Classical

def pivot (i : Fin 5) : Exp := Finsupp.single i (cutoff i)

abbrev Slots (i : Fin 5) := {d : Row // pivot i ≤ exp d}
abbrev ColumnIndex := (i : Fin 5) × Slots i

def offset (i : Fin 5) (d : Slots i) : Exp := exp d.val - pivot i

theorem offset_add (i : Fin 5) (d : Slots i) : offset i d + pivot i = exp d.val :=
  tsub_add_cancel_of_le d.property

theorem offset_injective (i : Fin 5) : Function.Injective (offset i) := by
  intro d e h
  apply Subtype.ext
  apply exp_injective
  rw [← offset_add i d, ← offset_add i e, h]

private theorem notTop (i : Fin 5) (d : Slots i) : d.val ≠ topRow := by
  intro h
  have hh := Finsupp.single_le_iff.mp d.property
  rw [h, exp_topRow, exponent_apply] at hh
  exact Nat.not_succ_le_self _ hh

private def preferred (c : ColumnIndex) : Fin 5 := chosen c.2.val (notTop c.1 c.2)

private def preferredColumn (c : ColumnIndex) : ColumnIndex :=
  ⟨preferred c, c.2.val, Finsupp.single_le_iff.mpr (chosen_le _ _)⟩

private theorem rowWeight (d : Row) : Finsupp.weight fullGrading (exp d) = (18, 2) := by
  rw [fullGrading_weight]
  apply Prod.ext
  · exact d.property.1
  · apply ZMod.val_injective 3
    rw [ZMod.val_natCast]
    exact d.property.2

private def rowOfWeight (a : Exp) (h : Finsupp.weight fullGrading a = (18, 2)) : Row := by
  rw [fullGrading_weight] at h
  apply rowOfExp a (congrArg Prod.fst h)
  have hc := congrArg (fun p : ℕ × ZMod 3 => p.2.val) h
  change ((↑(2 * a 0 + 2 * a 1 + a 2) : ZMod 3).val) = (2 : ZMod 3).val at hc
  rw [ZMod.val_natCast] at hc
  exact hc

private theorem rowOfWeight_exp (a : Exp) (h : Finsupp.weight fullGrading a = (18, 2)) :
    exp (rowOfWeight a h) = a := by
  unfold rowOfWeight
  apply exp_rowOfExp

private theorem pivotWeight (i : Fin 5) :
    Finsupp.weight fullGrading (pivot i) = (6 - (fullGrading i).1, -(fullGrading i).2) := by
  rw [pivot, Finsupp.weight_single]
  fin_cases i <;> decide

private def gradMul (a : Exp) (j : Fin 5) : FamilyPoly :=
  monomial a 1 * pderiv j universalF

private theorem gradMul_homogeneous (a : Exp) (j : Fin 5) :
    HG (gradMul a j) (Finsupp.weight fullGrading a + Finsupp.weight fullGrading (pivot j)) := by
  have hg := CycleQ2HiggsJacobianMembership.partial_homogeneous (RingHom.id CoeffRing) j
  rw [MvPolynomial.map_id] at hg
  rw [pivotWeight]
  exact (isWeightedHomogeneous_monomial fullGrading a _ rfl).mul hg

private theorem expand (i : Fin 5) (H : FamilyPoly)
    (hH : ∀ a, coeff a H ≠ 0 → ∃ d : Slots i, offset i d = a) :
    ∑ d : Slots i, coeff (offset i d) H • multiple d.val i = H * pderiv i universalF := by
  classical
  have hpoly : ∑ d : Slots i, coeff (offset i d) H •
      (monomial (offset i d) 1 : FamilyPoly) = H := by
    ext a
    simp only [coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul]
    by_cases he : ∃ d : Slots i, offset i d = a
    · obtain ⟨d, rfl⟩ := he
      rw [Finset.sum_eq_single d]
      · simp
      · intro e _ hne
        have hh := (offset_injective i).ne hne
        simp [hh]
      · simp
    · have hzero : coeff a H = 0 := by by_contra h; exact he (hH _ h)
      rw [hzero]
      apply Finset.sum_eq_zero
      intro d _
      have hd : offset i d ≠ a := fun h => he ⟨d, h⟩
      simp [hd]
  change (∑ d : Slots i, coeff (offset i d) H •
    ((monomial (offset i d) 1 : FamilyPoly) * pderiv i universalF)) = _
  simp_rw [← smul_mul_assoc]
  rw [← Finset.sum_mul, hpoly]

private def columnValue (c : ColumnIndex) : CoeffRing := trace (multiple c.2.val c.1)

private def component (i : Fin 5) (H : FamilyPoly) (c : ColumnIndex) : CoeffRing :=
  if c.1 = i then coeff (offset c.1 c.2) H else 0

private theorem component_pairing (i : Fin 5) (H : FamilyPoly)
    (hH : ∀ a, coeff a H ≠ 0 → ∃ d : Slots i, offset i d = a) :
    ∑ c : ColumnIndex, columnValue c * component i H c = trace (H * pderiv i universalF) := by
  classical
  rw [← expand i H hH, map_sum, Fintype.sum_sigma]
  simp only [component, mul_ite, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp only [if_true, map_smul, smul_eq_mul, columnValue, mul_comm]
  · intro j _ hj
    simp only [if_neg hj, Finset.sum_const_zero]
  · simp

private def common (c : ColumnIndex) : Exp := offset c.1 c.2 - pivot (preferred c)

private theorem preferred_le_offset (c : ColumnIndex) (h : c.1 ≠ preferred c) :
    pivot (preferred c) ≤ offset c.1 c.2 := by
  apply Finsupp.single_le_iff.mpr
  have ht := chosen_le c.2.val (notTop c.1 c.2)
  change cutoff (preferred c) ≤ exp c.2.val (preferred c) at ht
  simpa [offset, pivot, Finsupp.tsub_apply, Finsupp.single_eq_of_ne h.symm] using ht

private theorem common_right (c : ColumnIndex) (h : c.1 ≠ preferred c) :
    common c + pivot (preferred c) = offset c.1 c.2 :=
  tsub_add_cancel_of_le (preferred_le_offset c h)

private theorem common_left (c : ColumnIndex) (h : c.1 ≠ preferred c) :
    common c + pivot c.1 = offset (preferredColumn c).1 (preferredColumn c).2 := by
  have hh : common c + pivot c.1 + pivot (preferred c) =
      offset (preferredColumn c).1 (preferredColumn c).2 + pivot (preferredColumn c).1 := by
    rw [add_right_comm, common_right c h, offset_add, offset_add]
    rfl
  exact add_right_cancel hh

private theorem supported (c : ColumnIndex) (a : Exp) (j : Fin 5)
    (h : a + pivot j = offset c.1 c.2) :
    ∀ b, coeff b (gradMul a j) ≠ 0 → ∃ d : Slots c.1, offset c.1 d = b := by
  intro b hb
  have hw := gradMul_homogeneous a j hb
  have ht : Finsupp.weight fullGrading (b + pivot c.1) = (18, 2) := by
    rw [map_add, hw, ← map_add, h, ← map_add, offset_add, rowWeight]
  let row := rowOfWeight (b + pivot c.1) ht
  have hv : exp row = b + pivot c.1 := rowOfWeight_exp _ ht
  have hd : pivot c.1 ≤ exp row := by rw [hv]; exact le_add_self
  exact ⟨⟨row, hd⟩, by simp [offset, hv]⟩

private def unitColumn (c k : ColumnIndex) : CoeffRing := if k = c then 1 else 0

/-- The two-generator relations, completed by chosen columns to a square matrix. -/
private def relation (k c : ColumnIndex) : CoeffRing := by
  classical
  exact if c.1 = preferred c then unitColumn c k else
    component c.1 (gradMul (common c) (preferred c)) k -
    component (preferred c) (gradMul (common c) c.1) k +
    C (derivativeScalar c.1) * unitColumn (preferredColumn c) k

private theorem trace_preferred (c : ColumnIndex) : columnValue (preferredColumn c) = 0 :=
  trace_chosen c.2.val (notTop c.1 c.2)

private theorem unit_pairing (x : ColumnIndex) :
    ∑ k : ColumnIndex, columnValue k * unitColumn x k = columnValue x := by
  classical
  simp [unitColumn, mul_ite]

private theorem relation_pairing (c : ColumnIndex) :
    ∑ k : ColumnIndex, columnValue k * relation k c = 0 := by
  classical
  by_cases h : c.1 = preferred c
  · have ht := trace_chosen c.2.val (notTop c.1 c.2)
    change trace (multiple c.2.val (preferred c)) = 0 at ht
    simp only [relation, if_pos h, unit_pairing]
    change trace (multiple c.2.val c.1) = 0
    exact (congrArg (fun i : Fin 5 => trace (multiple c.2.val i)) h).trans ht
  · simp only [relation, if_neg h, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [show ∀ k : ColumnIndex, columnValue k *
        (C (derivativeScalar c.1) * unitColumn (preferredColumn c) k) =
        C (derivativeScalar c.1) * (columnValue k * unitColumn (preferredColumn c) k)
      from fun _ => mul_left_comm ..]
    have ht := component_pairing _ _ (supported (preferredColumn c) _ _ (common_left c h))
    change (∑ k : ColumnIndex, columnValue k * component (preferred c) (gradMul (common c) c.1) k) =
      trace (gradMul (common c) c.1 * pderiv (preferred c) universalF) at ht
    rw [← Finset.mul_sum, unit_pairing, trace_preferred, mul_zero, add_zero,
      component_pairing _ _ (supported c _ _ (common_right c h)), ht]
    have hc : gradMul (common c) (preferred c) * pderiv c.1 universalF =
        gradMul (common c) c.1 * pderiv (preferred c) universalF := by
      unfold gradMul
      ring
    rw [hc, sub_self]

private theorem component_seed (c k : ColumnIndex) (a : Exp) (j : Fin 5)
    (h : a + pivot j = offset c.1 c.2) :
    seedEvaluation (component c.1 (gradMul a j) k) =
      if k = c then derivativeScalar j else 0 := by
  classical
  obtain ⟨i, d⟩ := c
  obtain ⟨l, e⟩ := k
  by_cases hil : l = i
  · subst l
    simp only [component, if_true]
    rw [← coeff_map, gradMul, map_mul, map_monomial, map_one, ← pderiv_map,
      universalF_seed, derivative_eq, generator, X_pow_eq_monomial, C_mul_monomial,
      monomial_mul, one_mul, mul_one, coeff_monomial]
    change (if a + pivot j = offset i e then derivativeScalar j else 0) = _
    rw [h]
    by_cases hd : d = e
    · subst e; simp
    · have hne := (offset_injective i).ne hd
      simp [hne, Ne.symm hd]
  · have hne : (⟨l, e⟩ : ColumnIndex) ≠ ⟨i, d⟩ := fun hh => hil (congrArg Sigma.fst hh)
    simp [component, hil, hne]

private def relationMatrix : Matrix ColumnIndex ColumnIndex CoeffRing := Matrix.of relation
private def diagonalValue (c : ColumnIndex) : ℂ :=
  if c.1 = preferred c then 1 else derivativeScalar (preferred c)

private theorem relation_seed (k c : ColumnIndex) :
    seedEvaluation (relation k c) = if k = c then diagonalValue c else 0 := by
  classical
  by_cases h : c.1 = preferred c
  · simp [relation, h, unitColumn, diagonalValue, apply_ite]
  · have h₂ := component_seed (preferredColumn c) k _ _ (common_left c h)
    change seedEvaluation (component (preferred c) (gradMul (common c) c.1) k) =
      (if k = preferredColumn c then derivativeScalar c.1 else 0) at h₂
    simp only [relation, if_neg h, diagonalValue, map_add, map_sub, map_mul,
      component_seed c k _ _ (common_right c h), h₂]
    change _ - (if k = preferredColumn c then derivativeScalar c.1 else 0) +
      seedEvaluation (C (derivativeScalar c.1)) * seedEvaluation (unitColumn (preferredColumn c) k) = _
    simp only [CycleQ2GenericSexticGradient.seedEvaluation, eval_C, unitColumn, apply_ite, map_one, map_zero]
    split_ifs <;> ring

private theorem relation_det_ne_zero : relationMatrix.det ≠ 0 := by
  classical
  have hs : relationMatrix.map seedEvaluation = Matrix.diagonal diagonalValue := by
    ext k c
    rw [Matrix.diagonal_apply]
    by_cases he : k = c
    · subst c; exact (relation_seed k k).trans (by simp)
    · exact (relation_seed k c).trans (by simp [he])
  intro hz
  have hh := congrArg seedEvaluation hz
  rw [RingHom.map_det, map_zero] at hh
  change (relationMatrix.map seedEvaluation).det = 0 at hh
  rw [hs, Matrix.det_diagonal] at hh
  exact (Finset.prod_ne_zero_iff.mpr (fun c _ => by
    dsimp [diagonalValue]
    split <;> first | exact one_ne_zero | apply derivativeScalar_ne_zero)) hh

/-- The universal socle functional vanishes on every actual monomial Jacobian
multiple of the prescribed weighted degree and character. -/
theorem trace_multiple (d : Row) (i : Fin 5) (h : cutoff i ≤ exp d i) :
    trace (multiple d i) = 0 := by
  classical
  have hz : Matrix.vecMul columnValue relationMatrix = 0 := funext relation_pairing
  have hh := congrArg (fun v : ColumnIndex → CoeffRing => Matrix.vecMul v relationMatrix.adjugate) hz
  change Matrix.vecMul (Matrix.vecMul _ _) _ = Matrix.vecMul 0 _ at hh
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
    Matrix.zero_vecMul] at hh
  have hc := congrFun hh (⟨i, d, Finsupp.single_le_iff.mpr h⟩ : ColumnIndex)
  exact (mul_eq_zero.mp hc).resolve_left relation_det_ne_zero

end CycleQ2HiggsSocleSyzygies

namespace CycleQ2HiggsSocle
open CycleQ2FermatJacobian
theorem trace_multiple (d : Row) (i : Fin 5) (h : cutoff i ≤ exp d i) :
    trace (multiple d i) = 0 := CycleQ2HiggsSocleSyzygies.trace_multiple d i h
end CycleQ2HiggsSocle
end

#print axioms CycleQ2HiggsSocleSyzygies.trace_multiple
