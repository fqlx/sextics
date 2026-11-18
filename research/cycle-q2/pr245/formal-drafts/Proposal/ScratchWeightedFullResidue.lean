import Proposal.ScratchWeightedLiftClass
import Proposal.ScratchWeightedNativeChosenVertex
import Proposal.ScratchWeightedNativeChosenEvaluation

/-! The degree-three class of the full cubic pole on the proper universal
weighted threefold and its value in the native rational de Rham quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry
open CycleQ2.Cech CycleQ2CechDeRhamTotalThree CycleQ2WeightedNativeCech
open CycleQ2GeometricHodgeThreefold CycleQ2WeightedResidueAtlas
  CycleQ2WeightedGenericPointMap CycleQ2WeightedConeUniversal CycleQ2WeightedChosenResidue
namespace CycleQ2WeightedFullResidue

local notation "φ" => coefficients
open CycleQ2WeightedNativeTupleResidues in
def representative : Cycles (double φ) :=
  CycleQ2WeightedTupleCycle.cycle φ (vertex φ) (edge φ) (face φ)
    (vertex_closed φ) (edge_d φ) (face_d φ) (quadruple_closed φ)

theorem last_zero : representative.1.2.2.2 = 0 := rfl

theorem chosen_value :
    vertex (U φ) (Native.P (toBase φ) 3) chosen representative.1.1 = form :=
  CycleQ2WeightedNativeTupleResidues.chosen_vertex

theorem function_class : toFunctionField (classOf _ representative) = sourceClass :=
  evaluated_chosen representative chosen_value

variable [HasDerivedCategory (CycleQ2InjectiveCech.AbSheaf (threefold φ : TopCat))]

/-- The derived morphism on the proper threefold represented by the
logarithmic residue of its literal weighted cubic pole. -/
abbrev fullClass := CycleQ2WeightedLiftClass.proper φ representative last_zero goodParameter_unit

theorem primitive_of_fullClass_zero (h : fullClass = 0) :
    CycleQ2UniversalWeightedTransfer.UniversalWeightedPrimitiveExists :=
  CycleQ2WeightedLiftClass.primitive_of_vanishing representative last_zero chosen_value h

end CycleQ2WeightedFullResidue
end
#print axioms CycleQ2WeightedFullResidue.function_class
#print axioms CycleQ2WeightedFullResidue.primitive_of_fullClass_zero
