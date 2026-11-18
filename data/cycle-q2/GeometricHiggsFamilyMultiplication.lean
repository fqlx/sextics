import Proposal.GeometricHiggsFamilyGrading
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Trace duality and multiplication in the moving Jacobian quotient

The pairings use multiplication in the quotient by the five actual
weighted partial derivatives. The trace descends from the universal
degree-eighteen Macaulay row. The lower piece is separated by its pairing
with the upper piece on the common principal open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HiggsFamilyGrading

open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2IncidenceEquations (HG)
open CycleQ2HiggsJacobianFrames
open CycleQ2FermatJacobian (Exp exponent)
open CycleQ2FermatHiggs (basisMonomial tangentMonomial)
open CycleQ2HiggsSocle (H quotientTrace)
open CycleQ2HiggsGram (gram)
open MvPolynomial

variable {K : Type} [Field K] (φ : CoeffRing →+* K)

def pairing : Upper φ →ₗ[K] Lower φ →ₗ[K] K :=
  let tr : QuotientRing φ →ₗ[K] K := quotientTrace φ
  LinearMap.mk₂ K (fun x y => tr ((x : QuotientRing φ) * (y : QuotientRing φ)))
    (fun x y z => by simp [add_mul])
    (fun c x y => by simp [smul_mul_assoc])
    (fun x y z => by simp [mul_add])
    (fun c x y => by simp [mul_smul_comm])

theorem product_mem (x : Upper φ) (t : Tangent φ) :
    (x : QuotientRing φ) * (t : QuotientRing φ) ∈ Lower φ := by
  obtain ⟨p, hp, he₁⟩ := x.property
  obtain ⟨q, hq, he₂⟩ := t.property
  refine ⟨p * q, ?_, ?_⟩
  · have h := (show HG p (6,1) from hp).mul (show HG q (6,0) from hq)
    change HG (p * q) (12,1)
    exact (show ((6,1) + (6,0) : ℕ × ZMod 3) = (12,1) by decide) ▸ h
  · change (quotientMap φ) (p * q) = _
    rw [map_mul]
    exact congrArg₂ (· * ·) he₁ he₂

def higgs (t : Tangent φ) : Upper φ →ₗ[K] Lower φ where
  toFun x := ⟨(x : QuotientRing φ) * (t : QuotientRing φ), product_mem φ x t⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (smul_mul_assoc _ _ _)

theorem pairing_matrix (h : φ parameter ≠ 0) :
    LinearMap.toMatrix₂ (upperBasis φ h) (lowerBasis φ h) (pairing φ) =
      ((gram upperExp).map φ).transpose := by
  ext i j
  rw [LinearMap.toMatrix₂_apply]
  change quotientTrace φ
      ((upperBasis φ h i : QuotientRing φ) * (lowerBasis φ h j : QuotientRing φ)) =
    φ (gram upperExp j i)
  rw [upperBasis_coe, lowerBasis_coe, mul_comm, ← map_mul]
  exact (CycleQ2HiggsGram.gram_map_entry φ upperExp j i).symm

theorem pairing_flip_injective (h : φ parameter ≠ 0) : Function.Injective (pairing φ).flip := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.separatingRight_iff_flip_ker_eq_bot.mp
  apply (LinearMap.separatingRight_toMatrix₂_iff (upperBasis φ h) (lowerBasis φ h)).mp
  apply Matrix.separatingRight_iff_det_ne_zero.mpr
  rw [pairing_matrix φ h, Matrix.det_transpose]
  exact (φ.map_det (gram upperExp)) ▸ (factor_conditions φ h).2.2.2.1

theorem higgs_basis_entry (h : φ parameter ≠ 0) (m : Fin 35) (i j : Fin 33) :
    pairing φ (upperBasis φ h i) (higgs φ (tangentBasis φ h m) (upperBasis φ h j)) =
      φ (H m i j) := by
  change quotientTrace φ ((upperBasis φ h i : QuotientRing φ) *
    ((upperBasis φ h j : QuotientRing φ) * (tangentBasis φ h m : QuotientRing φ))) = _
  rw [upperBasis_coe, upperBasis_coe, tangentBasis_coe, ← mul_assoc, ← map_mul, ← map_mul]
  exact (CycleQ2HiggsSocle.H_quotientTrace φ m i j).symm

end CycleQ2HiggsFamilyGrading
end

#print axioms CycleQ2HiggsFamilyGrading.pairing_flip_injective
#print axioms CycleQ2HiggsFamilyGrading.higgs_basis_entry
