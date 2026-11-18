import Proposal.GeometricHodgeNormalCohomology
import Proposal.GeometricHodgeNormalDeformations
import Proposal.GeometricHodgeEulerTangentCoordinates
import Proposal.GeometricHodgeConnectingScalar

/-!
# Jacobian classes in the actual normal connecting homomorphism

A degree-six polynomial of a fixed character defines its section of O(6)
on the original threefold. The normal connecting morphism sends it to
an ordinary derived class. A coordinate derivative has its explicit
global velocity lift, so this map factors over the original graded
Jacobian quotient as a complex-linear map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeJacobianConnecting

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open CycleQ2GeometricIncidenceProj (homogeneous_of_character)
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeAtlasLine CycleQ2HodgeTwistRatios CycleQ2HodgeNormalDeformations
open CycleQ2HodgeInfinitesimalQuotient CycleQ2HodgeNormalCohomology
open CycleQ2GeometricAffineChartSections CycleQ2HodgeEulerChartBinding
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricSheafCohomologyScalar (cohomologyModule)
open CycleQ2HodgeConnectingScalar (sectionModule sectionBoundary)
open CycleQ2GenericSexticGradient (CoeffRing)

variable (φ : CoeffRing →+* ℂ) (χ : ZMod 3)

private abbrev coeff := schemeCoefficient (toBase φ)
local instance (V : (threefold φ).Opens) : Module ℂ Γ(twist φ 6,V) :=
  sectionModule (coeff φ) (twist φ 6) V
local instance : Module ℂ (H φ (rawTangent φ) 1) :=
  cohomologyModule (threefold φ).sheaf (coeff φ) (rawTangent φ) 1 ⊤

theorem evaluate_C (i : Fin 4) (V : (threefold φ).Opens) (h : V ≤ U φ i) (z : ℂ) :
    evaluate φ i V h (C z) = coefficientOn (threefold φ).sheaf (coeff φ) V z := by
  have h₁ := CycleQ2HodgeEulerTangentCoordinates.chartSection_eq_sectionMap φ i V h
    (algebraMap ℂ (CycleQ2HodgeEuler.chart φ i) z)
  have h₂ := chartSection_complex (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
    (Over.mk (homOfLE h)) z
  apply Eq.trans _ (h₁.symm.trans h₂)
  change sectionMap φ i V h ((chartEquiv φ i).symm
    (CycleQ2HodgeEuler.chartMap φ i (CycleQ2HodgeEuler.dehom i (algebraMap ℂ _ z)))) = _
  rw [AlgHom.commutes, AlgHom.commutes]

private theorem direction_component (i : Fin 4) (V : (threefold φ).Opens) (a : Directions ℂ χ) :
    component (cocycle φ 6) i V (directionSection φ a V) =
      evaluate φ i (V ⊓ U φ i) inf_le_right a.val := by
  change component _ i V (pack _ _ _ _) = _
  rw [component_pack, evaluate_homogeneous φ i _ _ a.val (homogeneous_of_character a.property)]

def sectionLinear (V : (threefold φ).Opens) : Directions ℂ χ →ₗ[ℂ] Γ(twist φ 6,V) where
  toFun a := directionSection φ a V
  map_add' a b := by
    apply component_injective (cocycle φ 6) V
    intro i
    rw [component_add, direction_component, direction_component, direction_component]
    exact map_add _ _ _
  map_smul' z a := by
    apply component_injective (cocycle φ 6) V
    intro i
    change component _ i V (directionSection φ (z • a) V) =
      component _ i V (coefficientOn (threefold φ).sheaf (coeff φ) V z • directionSection φ a V)
    rw [component_smul, direction_component, direction_component]
    change evaluate φ i (V ⊓ U φ i) inf_le_right (z • a.val) = _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, evaluate_C]
    exact congrArg (fun b : Γ(threefold φ,V ⊓ U φ i) => b * _) <|
      (ConcreteCategory.congr_hom ((CycleQ2GeometricDifferentialSheaf.coefficientMap
        (threefold φ).sheaf (coeff φ)).naturality (homOfLE (show V ⊓ U φ i ≤ V from inf_le_left)).op) z)

def polynomialClass (hg : IsUnit (φ goodParameter)) : Directions ℂ χ →ₗ[ℂ] H φ (rawTangent φ) 1 :=
  (sectionBoundary (coeff φ) (normalSequence φ) (addNormal_exact φ hg) ⊤).comp (sectionLinear φ χ ⊤)

theorem derivative_in_kernel (hg : IsUnit (φ goodParameter)) :
    (derivative φ χ).range ≤ (polynomialClass φ χ hg).ker := by
  rintro _ ⟨v,rfl⟩
  change connecting φ hg (directionSection φ (derivative φ χ v) ⊤) = 0
  exact (connecting_zero_iff φ hg _).mpr ⟨velocitySection φ v ⊤, normal_velocity φ v ⊤⟩

def jacobianClass (hg : IsUnit (φ goodParameter)) :
    CycleQ2HiggsJacobianFrames.gradedPiece φ 6 χ →ₗ[ℂ] H φ (rawTangent φ) 1 :=
  ((derivative φ χ).range.liftQ (polynomialClass φ χ hg) (derivative_in_kernel φ χ hg)).comp
    (quotientEquiv φ χ).symm.toLinearMap

theorem jacobianClass_direction (hg : IsUnit (φ goodParameter)) (p : Directions ℂ χ) :
    jacobianClass φ χ hg (directionClass φ χ p) = connecting φ hg (directionSection φ p ⊤) := by
  rw [← quotientEquiv_mk φ χ p]
  change (derivative φ χ).range.liftQ _ _ ((quotientEquiv φ χ).symm ((quotientEquiv φ χ) _)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end CycleQ2HodgeJacobianConnecting
end

#print axioms CycleQ2HodgeJacobianConnecting.jacobianClass_direction
