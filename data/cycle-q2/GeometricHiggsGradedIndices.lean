import Proposal.GeometricHiggsJacobianFrames
import Proposal.GeometricVariation

/-!
# Indices of the three graded Fermat monomial bases

The 33 upper, 35 tangent and 33 lower monomials used in the finite Higgs
calculation label exactly the bounded columns of the corresponding graded
Jacobian frames. The lower label retains its complementary socle exponent.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricHiggsGradedIndices

open CycleQ2HiggsJacobianFrames CycleQ2IncidenceNormalForm CycleQ2FermatHiggs
open CycleQ2FermatJacobian (Exp BoundedExp exponent bounded)
open CycleQ2FermatVariationAlgebra (lowerExponent lowerExponent_properties)

/-- The previous natural-number character is the canonical residue of the
character in the full grading. -/
theorem weight_eq_iff (e : Exp) (n : ℕ) (χ : ZMod 3) :
    Finsupp.weight fullGrading e = (n, χ) ↔
      weightedDegree e = n ∧ character e = χ.val := by
  rw [fullGrading_weight, Prod.mk.injEq]
  apply and_congr Iff.rfl
  constructor
  · intro he
    exact (ZMod.val_natCast 3 _).symm.trans (congrArg ZMod.val he)
  · intro he
    apply ZMod.val_injective
    exact (ZMod.val_natCast 3 _).trans he

private def label {n : ℕ} {χ : ZMod 3} (e : BoundedExp)
    (hw : Finsupp.weight fullGrading e.val = (n, χ)) : Bounded n χ := by
  let h := exists_index e.val hw
  refine ⟨h.choose, ?_⟩
  intro i
  rw [h.choose_spec]
  exact Nat.lt_succ_of_le (e.property i)

private theorem exp_label {n : ℕ} {χ : ZMod 3} (e : BoundedExp)
    (hw : Finsupp.weight fullGrading e.val = (n, χ)) :
    exp (label e hw).val = e.val :=
  (exists_index e.val hw).choose_spec

private def enumeration {ι : Type} (n : ℕ) (χ : ZMod 3)
    (v : ι → BoundedExp) (hinj : Function.Injective v)
    (hw : ∀ i, weightedDegree (v i).val = n ∧ character (v i).val = χ.val)
    (hall : ∀ e : Exp, e ∈ bounded → weightedDegree e = n → character e = χ.val →
      ∃ i, (v i).val = e) : ι ≃ Bounded n χ :=
  Equiv.ofBijective (fun i => label (v i) ((weight_eq_iff _ _ _).mpr (hw i))) (by
    constructor
    · intro i j hij
      apply hinj
      apply Subtype.ext
      simpa only [exp_label] using congrArg (fun e : Bounded n χ => exp e.val) hij
    · intro e
      have he := (weight_eq_iff (exp e.val) n χ).mp e.val.property
      obtain ⟨i, hi⟩ := hall (exp e.val) (fun k => Nat.le_of_lt_succ (e.property k)) he.1 he.2
      refine ⟨i, Subtype.ext (exp_injective ?_)⟩
      exact (exp_label _ _).trans hi)

/-- Upper degree-six character-one classes in the matrix order. -/
def upperIndex : Fin 33 ≃ Bounded 6 1 :=
  enumeration 6 1 CycleQ2FermatJacobian.basisIndex CycleQ2FermatJacobian.basisIndex_injective
    (fun i => ⟨(basis_properties i).1, (basis_properties i).2.1⟩)
    CycleQ2FermatJacobian.basis_complete_bounded

/-- Character-zero tangent directions in the matrix order. -/
def tangentIndex : Fin 35 ≃ Bounded 6 0 :=
  enumeration 6 0 CycleQ2FermatJacobian.tangentIndex CycleQ2FermatJacobian.tangentIndex_injective
    (fun i => ⟨(tangent_properties i).1, (tangent_properties i).2.1⟩)
    CycleQ2FermatJacobian.tangent_complete_bounded

/-- Complementary lower degree-twelve character-one classes in the dual upper order. -/
def lowerIndex : Fin 33 ≃ Bounded 12 1 :=
  enumeration 12 1 CycleQ2FermatVariationAlgebra.lowerIndex
    CycleQ2FermatVariationAlgebra.lowerIndex_injective
    (fun i => ⟨(lowerExponent_properties i).1, (lowerExponent_properties i).2.1⟩)
    CycleQ2FermatVariationAlgebra.lower_complete_bounded

@[simp] theorem exp_upperIndex (i : Fin 33) :
    exp (upperIndex i).val = exponent (basisMonomial i) :=
  exp_label (CycleQ2FermatJacobian.basisIndex i)
    ((weight_eq_iff _ 6 1).mpr ⟨(basis_properties i).1, (basis_properties i).2.1⟩)

@[simp] theorem exp_tangentIndex (m : Fin 35) :
    exp (tangentIndex m).val = exponent (tangentMonomial m) :=
  exp_label (CycleQ2FermatJacobian.tangentIndex m)
    ((weight_eq_iff _ 6 0).mpr ⟨(tangent_properties m).1, (tangent_properties m).2.1⟩)

@[simp] theorem exp_lowerIndex (i : Fin 33) :
    exp (lowerIndex i).val = exponent (lowerExponent i) :=
  exp_label (CycleQ2FermatVariationAlgebra.lowerIndex i)
    ((weight_eq_iff _ 12 1).mpr ⟨(lowerExponent_properties i).1, (lowerExponent_properties i).2.1⟩)

theorem exp_lowerIndex_eq_sub (i : Fin 33) :
    exp (lowerIndex i).val = exponent socle - exponent (basisMonomial i) := by
  rw [exp_lowerIndex]
  ext k
  rfl

end CycleQ2GeometricHiggsGradedIndices
end

#print axioms CycleQ2GeometricHiggsGradedIndices.upperIndex
#print axioms CycleQ2GeometricHiggsGradedIndices.tangentIndex
#print axioms CycleQ2GeometricHiggsGradedIndices.exp_lowerIndex_eq_sub
