import Proposal.GeometricGenericWeightedSpatialIndependence
import Proposal.GeometricGenericWeightedMonicDensity
import Proposal.GeometricMonicWeightedPrimitiveSpecialization
import Proposal.GeometricUniversalWeightedPrimitive

/-!
# Spatial denominators on the actual deformed pencil

A multiple in the three free spatial coordinates detects a denominator in the
monic chart ring. If one coefficient of the multiple survives the chosen pencil,
algebraic independence makes its evaluation and hence the denominator nonzero.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3500
noncomputable section
namespace CycleQ2GenericWeightedSpatialDenominator

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2GenericPencilLift
  CycleQ2GenericSpecialization CycleQ2GenericWeightedCoordinates
  CycleQ2GenericWeightedMonicOpen CycleQ2GenericWeightedMonicCoefficients
  CycleQ2GenericWeightedMonicDensity CycleQ2MonicWeightedAffineEquation
  CycleQ2MonicWeightedPrimitiveIdentity CycleQ2MonicWeightedPrimitiveSpecialization
open CycleQ2GenericPencilOpen (ParameterIndex)
open CycleQ2GenericWeightedOpen (coefficientPoint)

variable (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0)
local notation "ep" => endpointDirection c hc

/-- The universal monic coefficients specialized to the two-parameter field. -/
def coefficientSpecialization : Coeff →+* coefficientField ep :=
  (aeval (coefficients ep c)).toRingHom

theorem coe_coefficientSpecialization (p : Coeff) :
    (coefficientSpecialization c hc p : RF) =
      eval₂Hom (algebraMap ℂ RF) (normalizedCoefficientPoint ep c) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [coefficientSpecialization, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_C, eval₂Hom_C]
    rfl
  | add p q hp hq => simp only [map_add, IntermediateField.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, IntermediateField.coe_mul, hp, eval₂Hom_X']
    simp only [coefficientSpecialization, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_X, coefficients_coe]

theorem map_universal_affine :
    MvPolynomial.map (coefficientSpecialization c hc) universalAffine = monicEquation ep c := by
  rw [universalAffine, CycleQ2WeightedAffineChartJets.map_chart,
    CycleQ2UniversalSurfaceCoefficientMap.map_sextic]
  simp only [coefficientSpecialization, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    aeval_X, monicEquation]

theorem spatial_multiple_eval
    (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0)
    {d : Pol Coeff} {q : Coords Coeff}
    (hdiv : projection universalAffine d ∣ AdjoinRoot.of (separate universalAffine) q)
    (hq : MvPolynomial.map (coefficientSpecialization c hc) q ≠ 0) :
    value ep (MvPolynomial.map (coefficientSpecialization c hc) d) ≠ 0 := by
  let φ := coefficientSpecialization c hc
  let v := (value ep).comp (MvPolynomial.map φ)
  have hf : v universalAffine = 0 := by
    change value ep (MvPolynomial.map (coefficientSpecialization c hc) universalAffine) = 0
    rw [map_universal_affine]
    exact value_equation c hc hL
  apply evaluated_denominator_ne_zero hdiv φ hq v hf (![z 0, z 2, z 3] : Fin 3 → RF)
    (CycleQ2GenericWeightedSpatialIndependence.spatial_independent c hc hL)
  · intro a
    simp [v, value]
  · intro j
    change value ep (MvPolynomial.map φ (X j.castSucc)) = _
    rw [MvPolynomial.map_X]
    change eval₂Hom _ affinePoint (X j.castSucc) = _
    rw [eval₂Hom_X']
    fin_cases j <;> rfl

end CycleQ2GenericWeightedSpatialDenominator
end

#print axioms CycleQ2GenericWeightedSpatialDenominator.coe_coefficientSpecialization
#print axioms CycleQ2GenericWeightedSpatialDenominator.map_universal_affine
#print axioms CycleQ2GenericWeightedSpatialDenominator.spatial_multiple_eval
