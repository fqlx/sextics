import Proposal.ScratchWeightedNativeTupleResidues
import Proposal.ScratchLogChosenVertex

/-! The chosen vertex of the assembled proper cochain is the specified regular
form whose pullback to the generic point gives the requested original residue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedNativeTupleResidues
open CycleQ2WeightedResidueAtlas (U normalIndex)
open CycleQ2GeometricHodgeThreefold (toBase)
open CycleQ2WeightedConeUniversal (Base coefficients)
open CycleQ2WeightedGenericPointMap (chosen)
open CycleQ2WeightedSectionCochains (cochain actual_vertex readOn)
open CycleQ2HodgeEulerContractionRestriction (pull)
open scoped CycleQ2WeightedConeUniversal

/-- The value on the chosen chart of the genuine assembled vertex family,
with its signed Euler residue and the original cubic-pole normalization. -/
theorem chosen_vertex :
    CycleQ2.Cech.vertex (U coefficients) (CycleQ2.Cech.Native.P (toBase coefficients) 3) chosen
      (CycleQ2.Cech.assemble _ _ 0 3 (vertex coefficients)) = CycleQ2WeightedChosenResidue.form := by
  let ω := fun v : Fin 1 → CycleQ2WeightedResidueAtlas.Index =>
    CycleQ2ConeSimplexCochain.projectedVertex coefficients (normalIndex ∘ v)
  change CycleQ2.Cech.vertex _ _ chosen (cochain coefficients 0 3 ω) = _
  rw [actual_vertex]
  change pull _ 3 (-_) = _
  rw [map_neg]
  exact CycleQ2LogChosenVertex.source_eq_form

end CycleQ2WeightedNativeTupleResidues
end
#print axioms CycleQ2WeightedNativeTupleResidues.chosen_vertex
