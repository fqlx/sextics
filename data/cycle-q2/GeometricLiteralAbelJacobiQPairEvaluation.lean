import Proposal.GeometricLiteralAbelJacobiQAffineEvaluation
import Proposal.GeometricLiteralAbelJacobiQPairForms
import Proposal.GeometricLiteralAbelJacobiQPairReduction

/-!
# The mixed component of the pulled test cocycle in the actual pair rings

On the infinitesimal pair the sheaf evaluation of the original pulled
Čech section is the ordinary contraction of the native test two-form,
realized as a differential on the actual specialized pair. The formula
holds on each smaller common open of the ambient charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQPairEvaluation

open CategoryTheory Opposite AlgebraicGeometry CycleQ2LiteralAbelJacobiQPairCharts
  CycleQ2LiteralAbelJacobiQPairForms CycleQ2LiteralAbelJacobiQPairReduction
  CycleQ2LiteralAbelJacobiQAffineEvaluation CycleQ2LiteralAbelJacobiEvaluationAffine
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralThreefoldHodgeCech
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralThreefoldTestEdges CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2LiteralAmbientCharts

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower

local instance pairReductionAlgebra (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3) :
    Algebra (BPair t i k) (APair t i k) := (reduce t i k).toRingHom.toAlgebra
local instance pairReductionSMul (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3) :
    SMul (BPair t i k) (APair t i k) := (pairReductionAlgebra t i k).toSMul
local instance pairReductionModule (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3) :
    Module (BPair t i k) (APair t i k) := (pairReductionAlgebra t i k).toModule
local instance pairReductionTower (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3) :
    IsScalarTower ℂ (BPair t i k) (APair t i k) := IsScalarTower.of_algHom (reduce t i k)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V)

theorem eval_q_cocycle (i j : Fin 4) (hij : i < j) (W : Threefold.Opens)
    (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j)
    (v : Derivation ℂ (BPair t i (slot i j hij)) (APair t i (slot i j hij))) :
    let k := slot i j hij
    let O := (thickPairChart V t hV i k ≫ toThreefold V t) ⁻¹ᵁ W
    (evaluation v).val.app (op O)
        ((thickForms V t hV i k).val.app (op ((toThreefold V t) ⁻¹ᵁ W))
          (testEdgeValue V t i j W hi hj)) =
      (affineDifferentialSheaf (APair t i k)).val.map
        (homOfLE (show reduction (BPair t i k) (APair t i k) ⁻¹ᵁ O ≤ ⊤ from le_top)).op
        (globalForm (APair t i k) (contractRestrict v (edgeAt i k (pairMap i k (movingMap t i))))) := by
  dsimp only
  refine (congrArg ((evaluation v).val.app _) (thick_q_cocycle V t hV i j hij W hi hj)).trans ?_
  exact evaluate_native v _ _

end CycleQ2LiteralAbelJacobiQPairEvaluation
end

#print axioms CycleQ2LiteralAbelJacobiQPairEvaluation.eval_q_cocycle

