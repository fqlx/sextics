import Proposal.ScratchCechWeightedProperField
import Proposal.ScratchWeightedNativeFunctionClass
import Proposal.ScratchWeightedChosenResidue
import Proposal.ScratchWeightedFieldPointAnchor
import Proposal.WeightedConeGenericSmooth

/-! # From a vanishing proper weighted residue to the universal rational primitive

The point in the weighted threefold is the actual morphism from the spectrum
of the literal function field. Killing the proper hypercohomology class
annihilates the field value of the chosen residue. Its primitive belongs to
the exterior two-forms of that same field. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open CategoryTheory Opposite AlgebraicGeometry CycleQ2.Cech CycleQ2CechDeRhamTotalThree
open CycleQ2WeightedResidueAtlas CycleQ2WeightedConeUniversal CycleQ2WeightedGenericPointMap
  CycleQ2WeightedNativeCech CycleQ2GeometricHodgeThreefold
open CycleQ2WeightedChosenResidue (form genericPoint_form)
open CycleQ2WeightedFieldPointAnchor (g overBase anchor evaluation_algHom)
open scoped CycleQ2WeightedConeUniversal
namespace CycleQ2WeightedProperPrimitive

attribute [local instance] HasDerivedCategory.standard

variable (a : (double coefficients).X 0 3) (b : (double coefficients).X 1 2)
    (c : (double coefficients).X 2 1)
    (ha : (double coefficients).v 0 3 a = 0)
    (hb : (double coefficients).h 0 3 a = -((double coefficients).v 1 2 b))
    (hc : (double coefficients).h 1 2 b = (double coefficients).v 2 1 c)
    (hd : (double coefficients).h 2 1 c = 0)

/-- The semilinear restriction of regular three-forms at the chosen chart
recovers a primitive of the specified universal divergence numerator. -/
theorem primitive_of_proper_zero
    (hv : vertex (U coefficients) (Native.P (toBase coefficients) 3) chosen a = form)
    (hz : WeightedSheaf.properClass coefficients a b c ha hb hc hd goodParameter_unit = 0) :
    CycleQ2UniversalWeightedTransfer.UniversalWeightedPrimitiveExists := by
  obtain ⟨η,hη⟩ := WeightedSheaf.fieldPrimitive coefficients g overBase goodParameter_unit
    coordinateBasis spatial coordinateBasis_apply a b c ha hb hc hd hz chosen anchor
  rw [evaluation_algHom,hv,genericPoint_form] at hη
  apply class_zero_iff_primitive.mp
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨η,(field_derivative η).symm.trans hη⟩

end CycleQ2WeightedProperPrimitive
end

#print axioms CycleQ2WeightedProperPrimitive.primitive_of_proper_zero
