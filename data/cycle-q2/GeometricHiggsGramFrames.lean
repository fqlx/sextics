import Proposal.GeometricHiggsJacobianSpanning
import Proposal.GeometricHiggsSocleQuotient

/-!
# Monomial bases for the specialized weighted Jacobian components

The spanning determinant and the complementary Gram determinant give a
basis of each degree and character component of the full sextic Jacobian
quotient. Both determinants evaluate to one at the Fermat point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HiggsJacobianFrames

open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2HiggsGram

/-- Gram determinant for the Fermat-standard monomials of this bidegree. -/
def gramDet (n : ℕ) (χ : ZMod 3) : CoeffRing := by
  classical
  exact (gram (fun e : Bounded n χ => exp e.val)).det

theorem gramDet_seed (n : ℕ) (χ : ZMod 3) : seedEvaluation (gramDet n χ) = 1 := by
  classical
  apply gram_det_seed
  · exact exp_injective.comp Subtype.val_injective
  · intro e i
    exact Nat.le_of_lt_succ (e.property i)

variable {K : Type} [Field K] (φ : CoeffRing →+* K)

theorem boundedClass_independent {n : ℕ} {χ : ZMod 3} (hd : φ (gramDet n χ) ≠ 0) :
    LinearIndependent K (boundedClass φ (n := n) (χ := χ)) := by
  classical
  exact (independent_mod_ideal φ (fun e : Bounded n χ => exp e.val) (jacobian φ)
    (CycleQ2HiggsSocle.traceAt_mem_ideal φ) hd).1

/-- The basis lies in the image of actual weighted homogeneous polynomials in the quotient. -/
def basis (n : ℕ) (χ : ZMod 3) (hframe : IsUnit (φ (frameDet n χ))) (hgram : φ (gramDet n χ) ≠ 0) :
    Module.Basis (Bounded n χ) K (gradedPiece φ n χ) :=
  (Module.Basis.span (boundedClass_independent φ hgram)).map
    (LinearEquiv.ofEq _ _ (gradedPiece_eq_span φ hframe).symm)

@[simp] theorem basis_coe (n : ℕ) (χ : ZMod 3) (hframe : IsUnit (φ (frameDet n χ)))
    (hgram : φ (gramDet n χ) ≠ 0) (e : Bounded n χ) :
    (basis φ n χ hframe hgram e : QuotientRing φ) = boundedClass φ e := by
  simp [basis]

theorem gradedPiece_finrank (n : ℕ) (χ : ZMod 3) (hframe : IsUnit (φ (frameDet n χ)))
    (hgram : φ (gramDet n χ) ≠ 0) : Module.finrank K (gradedPiece φ n χ) = Nat.card (Bounded n χ) := by
  classical
  rw [Module.finrank_eq_card_basis (basis φ n χ hframe hgram), Nat.card_eq_fintype_card]

end CycleQ2HiggsJacobianFrames
end

#print axioms CycleQ2HiggsJacobianFrames.gramDet_seed
#print axioms CycleQ2HiggsJacobianFrames.basis_coe
#print axioms CycleQ2HiggsJacobianFrames.gradedPiece_finrank
