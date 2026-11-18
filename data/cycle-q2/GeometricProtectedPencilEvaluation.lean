import Proposal.GeometricProtectedPencilParameter
import Proposal.GeometricProtectedGenericPencilModel

/-!
# Coordinates of the generic pencil in the protected function field

On the protected affine chart X₀ = 1, the ordinary last coordinate is X₂
and the weighted last coordinate is X₂². Substitution respects both defining
equations and the map from the weighted model to the ordinary model.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2ProtectedPencilEvaluation

open MvPolynomial CycleQ2AffineWeightedTransfer
open CycleQ2ProtectedPencilParameter (evaluation evaluation_X)

abbrev Coeff := CycleQ2ProtectedGenericPencilModel.K
abbrev PolyRing := CycleQ2ProtectedGenericPencilModel.P

/-- Scalar action by evaluation at Y₂/X₂. -/
local instance : Algebra Coeff K := CycleQ2ProtectedPencilParameter.pencilAlgebra
local instance : IsScalarTower ℂ Coeff K :=
  IsScalarTower.of_algebraMap_eq fun c => (evaluation.commutes c).symm

private theorem parameter_image :
    algebraMap Coeff K CycleQ2ProtectedGenericPencilModel.parameter = parameter :=
  evaluation_X

def ordinaryCoordinates : Fin 5 → K := ![1, z 0, z 2, z 3, u]
def weightedCoordinates : Fin 5 → K := ![1, z 0, z 2, z 3, u^2]

def ordinaryPolynomial : PolyRing →ₐ[Coeff] K := aeval ordinaryCoordinates
def weightedPolynomial : PolyRing →ₐ[Coeff] K := aeval weightedCoordinates

theorem ordinaryPolynomial_square :
    ordinaryPolynomial.comp CycleQ2ProtectedGenericPencilModel.square = weightedPolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [ordinaryPolynomial, weightedPolynomial, ordinaryCoordinates,
    weightedCoordinates, CycleQ2ProtectedGenericPencilModel.square]

/-- The pencil restriction evaluates to the original six homogeneous coordinates
of the protected affine chart, including its last coordinate Y₂. -/
theorem ordinaryPolynomial_restrictProtected :
    (ordinaryPolynomial.restrictScalars ℂ).comp CycleQ2ProtectedGenericPencilModel.restrictProtected =
      aeval (![1, z 0, u, z 2, z 3, v] : Fin 6 → K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [ordinaryPolynomial, ordinaryCoordinates,
    CycleQ2ProtectedGenericPencilModel.restrictProtected, parameter_image, parameter_mul_u]

theorem weightedPolynomial_G : weightedPolynomial CycleQ2ProtectedGenericPencilModel.G = 0 := by
  calc
    _ = weightedEquation (z 0) (z 2) (z 3) (u^2) parameter := by
      have h₂ : algebraMap Coeff K 2 = 2 := map_ofNat _ 2
      simp [CycleQ2ProtectedGenericPencilModel.G, weightedPolynomial, weightedCoordinates,
        parameter_image, weightedEquation, h₂]
      ring
    _ = 0 := weighted_equation

theorem ordinaryPolynomial_F :
    ordinaryPolynomial (CycleQ2ProtectedGenericPencilModel.restrictProtected HodgeSubmission.F) = 0 := by
  rw [CycleQ2ProtectedGenericPencilModel.restrictProtected_F]
  exact (AlgHom.congr_fun ordinaryPolynomial_square _).trans weightedPolynomial_G

private def descend (p : PolyRing) (f : PolyRing →ₐ[Coeff] K) (h : f p = 0) :
    (PolyRing ⧸ Ideal.span {p}) →ₐ[Coeff] K :=
  Ideal.Quotient.liftₐ _ f (by
    intro q hq
    obtain ⟨b,rfl⟩ := Ideal.mem_span_singleton.mp hq
    simp [h])

def ordinary : (PolyRing ⧸ Ideal.span {CycleQ2ProtectedGenericPencilModel.restrictProtected HodgeSubmission.F})
    →ₐ[Coeff] K := descend _ ordinaryPolynomial ordinaryPolynomial_F

def weighted : CycleQ2ProtectedGenericPencilModel.QuotientRing →ₐ[Coeff] K :=
  descend _ weightedPolynomial weightedPolynomial_G

theorem ordinary_square (p : PolyRing) :
    ordinary (Ideal.Quotient.mk _ (CycleQ2ProtectedGenericPencilModel.square p)) =
      weighted (CycleQ2ProtectedGenericPencilModel.quotient p) :=
  AlgHom.congr_fun ordinaryPolynomial_square p

end CycleQ2ProtectedPencilEvaluation
end

#print axioms CycleQ2ProtectedPencilEvaluation.ordinaryPolynomial_restrictProtected
#print axioms CycleQ2ProtectedPencilEvaluation.ordinary_square
