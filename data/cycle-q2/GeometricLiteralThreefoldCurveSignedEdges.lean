import Proposal.GeometricLiteralThreefoldCurveGermEvaluation
import Proposal.GeometricLiteralThreefoldCurveAdjunction
import Proposal.GeometricLiteralThreefoldCurveGermCover

/-!
# The signed Čech coboundary on the original twelve curve vertices

The actual evaluated threefold edge plus the terminal correction equals
the initial correction minus the pulled cubic contraction. This includes
the pairs of native vertices having the same ambient chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralThreefoldCurveSignedEdges

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricSheafLocalIso CycleQ2FiniteCechDescent CycleQ2FiniteInjectiveCech CycleQ2FiniteCechRefinement
  CycleQ2LiteralThreefoldCurveGermCover CycleQ2LiteralThreefoldCurveGermEvaluation CycleQ2LiteralThreefoldCurveGermEdge
  CycleQ2LiteralThreefoldCurveAdjunction CycleQ2LiteralThreefoldCurveAdaptedValue CycleQ2LiteralThreefoldCurveVertexCochain
  CycleQ2LiteralThreefoldCurveEvaluationRefinement CycleQ2LiteralThreefoldCurveClassRepresentative
  CycleQ2LiteralThreefoldVertexPointBinding CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralThreefoldHodgeCech
  CycleQ2LiteralAbelJacobiEvaluationDerived CycleQ2LiteralMovingResidueCurve CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralProjectiveIntersections
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2SeedSectionSheafCurveBinding
  CycleQ2GeometricSectionDifferentials

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
  (u v : Vertex)

private theorem same_index {i j : Fin 4} (h : i = j) (W : (Curve t).Opens)
    (hi : W ≤ testCover t V hV i) (hj : W ≤ testCover t V hV j) :
    edgeValue (curveForms t) (testCover t V hV) (evaluatedTest t ht V hV) i j W hi hj = 0 := by
  subst j
  exact oneCocycle_diagonal _ (evaluatedTest_closed t ht V hV) i W hi

theorem signed_edges (huv : chartIndex u ≤ chartIndex v) (W : (Curve t).Opens)
    (huW : W ≤ vertexOpen t u) (hvW : W ≤ vertexOpen t v) :
    edgeValue (curveForms t) (vertexOpen t) (nativeTest t V hV ht) u v W huW hvW +
      res (curveForms t) hvW (corrections t ht v) =
    res (curveForms t) huW (corrections t ht u) -
      edgeValue (curveForms t) (vertexOpen t) (beta t) u v W huW hvW := by
  apply signed_edges_on_germ
  intro m n G ha huG hvG huZ hvZ hJ
  let Z := seedOpen t G
  let s : Finset Vertex := {u,v}
  have hu : u ∈ s := by simp [s]
  have hv : v ∈ s := by simp [s]
  have es : closedOpen s = cover u ⊓ cover v := by simp [s,closedOpen_eq,cover]
  have hZ : Z ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s := by
    rw [es, Scheme.Hom.preimage_inf]
    exact le_inf huZ hvZ
  let τ := toSheaf (Curve t).sheaf (curveCoefficient t) Z
  have hA := adapted_below_jacobian t ht s u v hu hv m n Z hZ hJ
  have xu := corrections_on_intersection t ht s u hu Z hZ
  have xv := corrections_on_intersection t ht s v hv Z hZ
  rw [xu,xv]
  rcases huv.lt_or_eq with lt | eq
  · have h₁ := evaluated_edge t ht V hV s u v hu hv lt G huG hvG hZ
    have h₂ := congrArg τ (corrected_on_germ t ht V hV s u v hu hv G huG hvG
      (slot _ _ lt) (succAbove_slot _ _ lt) hZ ha)
    change τ (_ + _) = τ (_ + _) at h₂
    rw [map_add, map_add] at h₂
    rw [h₁]
    exact h₂.trans ((congrArg (τ (rawVertex t ht s u hu Z hZ) + ·) hA).trans (sub_eq_add_neg _ _).symm)
  · have h₁ := (nativeTest_edge t V hV ht u v Z huZ hvZ).trans (same_index t ht V hV eq Z _ _)
    have h₂ := congrArg τ (same_chart t ht s u v hu hv Z hZ eq)
    change τ _ = τ (_ + _) at h₂
    rw [map_add] at h₂
    rw [h₁,zero_add]
    exact h₂.trans ((congrArg (τ (rawVertex t ht s u hu Z hZ) + ·) hA).trans (sub_eq_add_neg _ _).symm)

end CycleQ2LiteralThreefoldCurveSignedEdges
end

#print axioms CycleQ2LiteralThreefoldCurveSignedEdges.signed_edges
