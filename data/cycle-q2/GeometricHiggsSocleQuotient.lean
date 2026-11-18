import Proposal.GeometricHiggsSocleSyzygies
import Proposal.GeometricHiggsGram
import Proposal.GeometricHiggsJacobianMembership

/-!
# The socle trace on the actual specialized Jacobian ring

An arbitrary polynomial in the Jacobian ideal has homogeneous multipliers
for its degree-18, character-2 component. Every monomial of those multipliers
gives one of the columns annihilated by the universal Koszul relations. The
polynomial trace consequently descends to the entire Jacobian quotient after
every coefficient specialization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HiggsSocle

open MvPolynomial CycleQ2FermatHiggs CycleQ2FermatJacobian CycleQ2GenericSexticGradient
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

variable {K : Type*} [CommRing K] (φ : CoeffRing →+* K)

abbrev specializedJacobian : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.span (Set.range fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF))

private theorem row_after_cutoff (i : Fin 5) (m : Exp)
    (hm : Finsupp.weight fullGrading m =
      (18 - (6 - (fullGrading i).1), 2 + (fullGrading i).2)) :
    ∃ d : Row, exp d = m + Finsupp.single i (cutoff i) := by
  let a := m + Finsupp.single i (cutoff i)
  have hg : Finsupp.weight fullGrading a = (18, 2) := by
    rw [show a = m + Finsupp.single i (cutoff i) from rfl, map_add, hm, Finsupp.weight_single]
    fin_cases i <;> decide
  rw [fullGrading_weight] at hg
  have hd : weightedDegree a = 18 := congrArg Prod.fst hg
  have hc := congrArg (fun z : ℕ × ZMod 3 => z.2.val) hg
  change ((2 * a 0 + 2 * a 1 + a 2 : ℕ) : ZMod 3).val = 2 at hc
  rw [ZMod.val_natCast] at hc
  exact ⟨rowOfExp a hd hc, exp_rowOfExp a hd hc⟩

private theorem monomial_partial_trace (i : Fin 5) (m : Exp) (c : K)
    (hm : Finsupp.weight fullGrading m =
      (18 - (6 - (fullGrading i).1), 2 + (fullGrading i).2)) :
    traceAt φ (monomial m c * pderiv i (MvPolynomial.map φ universalF)) = 0 := by
  obtain ⟨d, hd⟩ := row_after_cutoff i m hm
  have hi : cutoff i ≤ exp d i := by
    rw [hd, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  have hz := traceAt_multiple φ d i
  rw [trace_multiple d i hi, map_zero, hd, add_tsub_cancel_right] at hz
  have hc : monomial m c = c • (monomial m 1 : MvPolynomial (Fin 5) K) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, smul_mul_assoc, map_smul, hz, smul_zero]

/-- All Jacobian-ideal elements have zero trace after arbitrary specialization. -/
theorem traceAt_mem_ideal (p : MvPolynomial (Fin 5) K) (hp : p ∈ specializedJacobian φ) :
    traceAt φ p = 0 := by
  classical
  obtain ⟨h, hh, _, hcomponent⟩ :=
    CycleQ2HiggsJacobianMembership.component_multipliers φ 18 2 p hp
  rw [← CycleQ2HiggsGram.traceAt_component φ p, hcomponent, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [(h i).as_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  exact monomial_partial_trace φ i m _ (hh i (mem_support_iff.mp hm))

def quotientTrace : (MvPolynomial (Fin 5) K ⧸ specializedJacobian φ) →ₗ[K] K :=
  ((specializedJacobian φ).restrictScalars K).liftQ (traceAt φ)
    (fun p hp => traceAt_mem_ideal φ p hp)

@[simp] theorem quotientTrace_mk (p : MvPolynomial (Fin 5) K) :
    quotientTrace φ (Ideal.Quotient.mk (specializedJacobian φ) p) = traceAt φ p := rfl

theorem quotientTrace_socle :
    quotientTrace φ (Ideal.Quotient.mk (specializedJacobian φ)
      (monomial (exponent socle) 1)) = φ macaulay.det := by
  have h := map_trace φ (monomial (exponent socle) 1)
  rw [trace_socle, map_monomial, map_one] at h
  exact h.symm

/-- The family Higgs matrix consists of trace values of actual Jacobian-quotient classes. -/
theorem H_quotientTrace (m : Fin 35) (i j : Fin 33) :
    (H m).map φ i j =
      quotientTrace φ (Ideal.Quotient.mk (specializedJacobian φ) (triple K m i j)) := by
  have h := map_trace φ (triple CoeffRing m i j)
  simp only [triple, map_mul, map_monomial, map_one] at h
  exact h

end CycleQ2HiggsSocle
end

#print axioms CycleQ2HiggsSocle.traceAt_mem_ideal
#print axioms CycleQ2HiggsSocle.quotientTrace_mk

#print axioms CycleQ2HiggsSocle.H_quotientTrace
