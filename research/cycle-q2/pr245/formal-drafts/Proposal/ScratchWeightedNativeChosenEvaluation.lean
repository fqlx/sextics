import Proposal.ScratchWeightedNativeFunctionClass
import Proposal.ScratchWeightedChosenResidue

/-! The actual regular volume form at the selected weighted vertex yields
the class whose vanishing is the universal primitive statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CycleQ2.Cech CycleQ2CechDeRhamTotalThree CycleQ2WeightedResidueAtlas
open CycleQ2WeightedChosenResidue CycleQ2WeightedGenericPointMap CycleQ2WeightedConeUniversal
  CycleQ2GeometricHodgeThreefold

namespace CycleQ2WeightedNativeCech

theorem evaluated_chosen (z : Cycles (double coefficients))
    (hz : vertex (U coefficients) (Native.P (toBase coefficients) 3) chosen z.1.1 = form) :
    toFunctionField (classOf _ z) = sourceClass := by
  change Submodule.Quotient.mk
    (CycleQ2LogarithmicChartDerivative.pull genericPoint 3
      (vertex (U coefficients) (Native.P (toBase coefficients) 3) chosen z.1.1)) =
    Submodule.Quotient.mk topForm
  rw [hz,genericPoint_form]

theorem primitive_of_chosen_total_zero (z : Cycles (double coefficients))
    (hv : vertex (U coefficients) (Native.P (toBase coefficients) 3) chosen z.1.1 = form)
    (hz : classOf _ z = 0) : CycleQ2UniversalWeightedTransfer.UniversalWeightedPrimitiveExists := by
  apply class_zero_iff_primitive.mp
  rw [← evaluated_chosen z hv,hz,map_zero]

end CycleQ2WeightedNativeCech
end

#print axioms CycleQ2WeightedNativeCech.evaluated_chosen
