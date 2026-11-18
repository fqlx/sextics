import Proposal.WeightedConeFermatParameter
import Proposal.WeightedConeUniversalModel
import Proposal.GeometricHodgeThreefoldSmooth

/-! Good reduction and smoothness on the actual monic coefficient function field. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeUniversal
open MvPolynomial AlgebraicGeometry CycleQ2GeometricHodgeThreefold
  CycleQ2MonicWeightedAffineEquation (Coeff)
  CycleQ2WeightedConeFermatParameter (integralParameters)

/-- The universal coefficient map factors through the polynomial parameter
ring before its injection into the coefficient field. -/
theorem coefficients_factor : liftCoeff.comp integralParameters = coefficients :=
  CycleQ2WeightedConeFermatParameter.parameters_map liftCoeff

theorem goodParameter_ne : coefficients goodParameter ≠ 0 := by
  rw [← coefficients_factor]
  exact fun h => CycleQ2WeightedConeFermatParameter.goodParameter_ne
    (IsFractionRing.to_map_eq_zero_iff.mp h)

theorem goodParameter_unit : IsUnit (coefficients goodParameter) :=
  isUnit_iff_ne_zero.mpr goodParameter_ne

theorem partial_ne (i : Fin 5) : pderiv i (equation coefficients) ≠ 0 := by
  intro he
  apply CycleQ2WeightedConeFermatParameter.partial_ne i
  apply MvPolynomial.map_injective liftCoeff (IsFractionRing.injective Coeff Base)
  rw [map_zero,← pderiv_map,CycleQ2WeightedConeFermatParameter.integralFull_map]
  rwa [full_equation] at he

theorem coordinate_cover : (⨆ i : Fin 4, coordinateOpen coefficients i) = ⊤ :=
  coordinateOpens_cover_of_good coefficients goodParameter_unit

theorem smooth_threefold : SmoothOfRelativeDimension 3 (toBase coefficients) :=
  toBase_smoothDimension coefficients goodParameter_unit

theorem proper_threefold : IsProper (toBase coefficients) := toBase_proper coefficients

end CycleQ2WeightedConeUniversal
end
#print axioms CycleQ2WeightedConeUniversal.goodParameter_unit
#print axioms CycleQ2WeightedConeUniversal.smooth_threefold
#print axioms CycleQ2WeightedConeUniversal.partial_ne

