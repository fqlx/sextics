import Proposal.GeometricHodgeFermatTangentCochain
import Proposal.GeometricHodgeFermatOverlapVolume
import Proposal.GeometricHodgeEulerTriplePairing

/-!
# Evaluation of three intrinsic Fermat normal-connecting cocycles

On any common subopen, evaluating the original projective volume on the
three ordered Čech edges multiplies their explicit determinant by the
inverse of the x₁ partial. Its value is twice the weight-two coordinate
times the three normalized numerators and the four inverse partials.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatYukawaEvaluation

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeTwistRatios (U)
open CycleQ2HodgeFermatNormalLifts (ψ)
open CycleQ2HodgeFermatCechBoundary (smooth_parameter)
open CycleQ2HodgeFermatTangentCochain (T representative edge_coordinates)
open CycleQ2HodgeFermatOverlapVolume (f forms coordIndex common_volume)
open CycleQ2HodgeFermatYukawaRows (d matrix row value w native_determinant)
open CycleQ2HodgeEulerContractionSheaf (evaluateOn)
open CycleQ2HodgeEulerTangentSheaf (cotangent tangent)
open CycleQ2HodgeEulerTriplePairing (pairing pairing_eval)
open CycleQ2HodgeEulerTripleContraction (triple_exterior_wedge)
open CycleQ2GeometricDifferentialChartTransport (chartTop)
open CycleQ2FiniteInjectiveCech (edgeValue)
open scoped Matrix

variable (V : (threefold ψ).Opens) (h : ∀ i : Fin 4, V ≤ U ψ i)

abbrev tangentEdge (p : grade ψ 6) (i j : Fin 4) : Γ(tangent f,V) :=
  edgeValue T (U ψ) (representative p) i j V (h i) (h j)

private theorem row_evaluation (p : grade ψ 6) (i j : Fin 4) :
    (fun k => evaluateOn (cotangent f) V (tangentEdge V h p i j) (chartTop V) (forms V h k)) =
      row V h i j p := by
  funext k
  exact edge_coordinates p i j V h k

theorem evaluation (p q r : grade ψ 6) :
    (pairing ψ smooth_parameter).eval V (tangentEdge V h p 0 1) (tangentEdge V h q 1 2)
      (tangentEdge V h r 2 3) = d V h 1 * (matrix V h p q r).det := by
  rw [pairing_eval, common_volume V h, triple_exterior_wedge, row_evaluation, row_evaluation,
    row_evaluation]
  rfl

theorem explicit_value (p q r : grade ψ 6) :
    (pairing ψ smooth_parameter).eval V (tangentEdge V h p 0 1) (tangentEdge V h q 1 2)
      (tangentEdge V h r 2 3) = 2 * (value V h p * value V h q * value V h r) *
        w V h * ∏ i, d V h i :=
  (evaluation V h p q r).trans (native_determinant V h p q r)

end CycleQ2HodgeFermatYukawaEvaluation
end
#print axioms CycleQ2HodgeFermatYukawaEvaluation.explicit_value
