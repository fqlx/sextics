import Proposal.GeometricLiteralThreefoldExteriorDescent
import Proposal.GeometricLiteralThreefoldDeformedEdgeDerivative

/-! The ordinary exterior differential on the original charts and their intersections. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldExteriorDescentNative

open CycleQ2LiteralThreefoldExteriorDescent CycleQ2LiteralThreefoldCartan
  CycleQ2LiteralThreefoldDeformedEdgeDerivative CycleQ2LiteralThreefoldDeformedOverlap
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldExteriorDerivative CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralThreefoldTestEdges

theorem chartSeparated (i : Fin 4) : Separated (T i) := by
  intro z t h
  apply chart_restrictions_injective i
  intro a
  let f := IsScalarTower.toAlgHom ℂ (T i) (Patch i a)
  have hz := h (Patch i a) f (basis i a) _ (basis_apply i a)
  change exteriorDifferentialMap f 3 (z - t) = additive (basis i a) (exteriorDifferentialMap f 2 0) at hz
  rwa [map_sub, map_zero, map_zero, sub_eq_zero] at hz

theorem overlapSeparated (i : Fin 4) (k : Fin 3) : Separated (FixedOverlap i k) := by
  intro z t h
  apply triple_restrictions_injective i k
  intro a b
  let f := κ i k a b
  have hz := h (Ring i k a b) f (basisOn i k a b) _ (basisOn_apply i k a b)
  change exteriorDifferentialMap f 3 (z - t) =
    additive (basisOn i k a b) (exteriorDifferentialMap f 2 0) at hz
  rwa [map_sub, map_zero, map_zero, sub_eq_zero] at hz

/-- The original test edge has the specified exterior derivative on the whole overlap. -/
theorem edge_differential (i : Fin 4) (k : Fin 3) :
    differential (overlapSeparated i k) (nativeEdge i k) = edgeDerivative i k := by
  apply triple_restrictions_injective i k
  intro a b
  exact (differential_represents (overlapSeparated i k) (nativeEdge i k)
    (Ring i k a b) (κ i k a b) (basisOn i k a b) _ (basisOn_apply i k a b)).trans
      (edgeDerivative_restrict i k a b).symm

end CycleQ2LiteralThreefoldExteriorDescentNative
end

#print axioms CycleQ2LiteralThreefoldExteriorDescentNative.edge_differential
