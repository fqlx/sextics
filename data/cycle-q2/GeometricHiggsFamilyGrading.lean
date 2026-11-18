import Proposal.GeometricHiggsGramFrames
import Proposal.GeometricHiggsGradedIndices
import Proposal.GeometricHiggsFamilyMinor

/-!
# Common Jacobian frames for the full sextic family

Three monomial frames and their trace-duality determinants cut out a single
principal open containing Fermat. On every field-valued fiber of this open
the upper and lower graded pieces of the actual Jacobian quotient each have
dimension 33, and its invariant degree-six tangent piece has dimension 35.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HiggsFamilyGrading

open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2HiggsJacobianFrames
open CycleQ2GeometricHiggsGradedIndices (upperIndex lowerIndex tangentIndex)
open CycleQ2FermatJacobian (Exp exponent)
open CycleQ2FermatHiggs (basisMonomial tangentMonomial basis_properties socle)
open CycleQ2HiggsGram (gram gram_det_seed)
open MvPolynomial

def upperExp (i : Fin 33) : Exp := exponent (basisMonomial i)

theorem upperExp_injective : Function.Injective upperExp := by
  intro i j h
  apply CycleQ2FermatHiggs.basis_injective
  funext k
  exact congrArg (fun x : Exp => x k) h

theorem upperExp_le (i : Fin 33) : upperExp i ≤ exponent socle := (basis_properties i).2.2

def frameParameter (n : ℕ) (χ : ZMod 3) : CoeffRing := frameDet n χ * gramDet n χ

def parameter : CoeffRing :=
  frameParameter 6 1 * (frameParameter 6 0 * (frameParameter 12 1 *
    ((gram upperExp).det * CycleQ2HiggsFamilyMinor.parameter)))

theorem parameter_seed : seedEvaluation parameter =
    CycleQ2GeometricHiggsCommutantOpen.minor CycleQ2GeometricHiggsCommutantOpen.fermat := by
  simp only [parameter, frameParameter, map_mul, seed_frameDet, gramDet_seed,
    gram_det_seed upperExp upperExp_injective upperExp_le, one_mul, CycleQ2HiggsFamilyMinor.parameter_seed]

theorem fermat_mem : CycleQ2GeometricHiggsCommutantOpen.fermatPoint ∈
    PrimeSpectrum.basicOpen parameter := by
  apply (PrimeSpectrum.mem_basicOpen _ _).mpr
  change seedEvaluation parameter ≠ 0
  rw [parameter_seed]
  exact CycleQ2GeometricHiggsCommutantOpen.fermat_minor_ne_zero

variable {K : Type} [Field K] (φ : CoeffRing →+* K)

theorem factor_conditions (h : φ parameter ≠ 0) :
    (φ (frameDet 6 1) ≠ 0 ∧ φ (gramDet 6 1) ≠ 0) ∧
    (φ (frameDet 6 0) ≠ 0 ∧ φ (gramDet 6 0) ≠ 0) ∧
    (φ (frameDet 12 1) ≠ 0 ∧ φ (gramDet 12 1) ≠ 0) ∧
    φ (gram upperExp).det ≠ 0 ∧ φ CycleQ2HiggsFamilyMinor.parameter ≠ 0 := by
  simpa only [parameter, frameParameter, map_mul, mul_ne_zero_iff] using h

abbrev Upper := gradedPiece φ 6 1
abbrev Lower := gradedPiece φ 12 1
abbrev Tangent := gradedPiece φ 6 0

def upperBasis (h : φ parameter ≠ 0) : Module.Basis (Fin 33) K (Upper φ) :=
  (basis φ 6 1 (isUnit_iff_ne_zero.mpr (factor_conditions φ h).1.1)
    (factor_conditions φ h).1.2).reindex upperIndex.symm

def tangentBasis (h : φ parameter ≠ 0) : Module.Basis (Fin 35) K (Tangent φ) :=
  (basis φ 6 0 (isUnit_iff_ne_zero.mpr (factor_conditions φ h).2.1.1)
    (factor_conditions φ h).2.1.2).reindex tangentIndex.symm

def lowerBasis (h : φ parameter ≠ 0) : Module.Basis (Fin 33) K (Lower φ) :=
  (basis φ 12 1 (isUnit_iff_ne_zero.mpr (factor_conditions φ h).2.2.1.1)
    (factor_conditions φ h).2.2.1.2).reindex lowerIndex.symm

theorem upperBasis_coe (h : φ parameter ≠ 0) (i : Fin 33) :
    (upperBasis φ h i : QuotientRing φ) = quotientMap φ (monomial (upperExp i) 1) := by
  simp [upperBasis, Module.Basis.reindex_apply, basis_coe, boundedClass, upperExp]

theorem tangentBasis_coe (h : φ parameter ≠ 0) (m : Fin 35) :
    (tangentBasis φ h m : QuotientRing φ) = quotientMap φ (monomial (exponent (tangentMonomial m)) 1) := by
  simp [tangentBasis, Module.Basis.reindex_apply, basis_coe, boundedClass]

theorem lowerBasis_coe (h : φ parameter ≠ 0) (i : Fin 33) :
    (lowerBasis φ h i : QuotientRing φ) = quotientMap φ
      (monomial (CycleQ2HiggsGram.complementExp (upperExp i)) 1) := by
  simp only [lowerBasis, Module.Basis.reindex_apply, Equiv.symm_symm, basis_coe,
    boundedClass, CycleQ2GeometricHiggsGradedIndices.exp_lowerIndex_eq_sub]
  rfl

theorem dimensions (h : φ parameter ≠ 0) :
    Module.finrank K (Upper φ × Lower φ) = 66 ∧ Module.finrank K (Tangent φ) = 35 := by
  let u := upperBasis φ h
  let l := lowerBasis φ h
  let t := tangentBasis φ h
  let := Module.Finite.of_basis u
  let := Module.Finite.of_basis l
  simp only [Module.finrank_prod, Module.finrank_eq_card_basis u, Module.finrank_eq_card_basis l,
    Module.finrank_eq_card_basis t, Fintype.card_fin, Nat.reduceAdd, and_self]

end CycleQ2HiggsFamilyGrading
end

#print axioms CycleQ2HiggsFamilyGrading.fermat_mem
#print axioms CycleQ2HiggsFamilyGrading.dimensions
