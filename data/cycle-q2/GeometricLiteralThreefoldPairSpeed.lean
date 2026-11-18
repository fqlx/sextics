import Proposal.GeometricLiteralThreefoldPairMotion
import Proposal.GeometricThreefoldMixedTimeVelocity
import Proposal.GeometricLiteralAbelJacobiQPairReductionKernel
import Proposal.GeometricLiteralAbelJacobiQPairSeed

/-!
# Independence of the mixed one-form on the literal affine projective pair

Any two velocities on the true first-order pair that agree on the time
parameter give the same mixed one-form for every test vector along the
closed curve. The closed-pair smoothness and the actual kernel of the
reduction supply the geometric hypotheses.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldPairSpeed

open CycleQ2LiteralThreefoldPairMotion CycleQ2ThreefoldMixedTimeVelocity
  CycleQ2LiteralAbelJacobiQPairCharts CycleQ2LiteralAbelJacobiQPairReductionKernel
  CycleQ2LiteralAbelJacobiQPairSeed CycleQ2ThreefoldContractionAlongMap CycleQ2ThreefoldMixedCurveForm
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
open scoped DualNumber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  reductionPairAlgebra reductionPairTower

attribute [local instance 2000] Algebra.toSMul Algebra.toModule

variable (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3)
private abbrev P := BPair t i k
private abbrev Q := APair t i k

/-- The genuine reduced pair is formally smooth over the complex numbers. -/
theorem pair_formallySmooth (ht : AlgebraicIndependent ℚ t) : Algebra.FormallySmooth ℂ (Q t i k) := by
  have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t
    (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht) i
  exact inferInstanceAs (Algebra.FormallySmooth ℂ (Localization.Away (toCurve t i (ratio i k))))

variable {R : Type} [CommRing R] [Algebra ℂ R] [Algebra R (P t i k)] [Algebra R (Q t i k)]
  [IsScalarTower ℂ R (P t i k)] [IsScalarTower ℂ R (Q t i k)]
  [IsScalarTower R (P t i k) (Q t i k)]

theorem pair_speed (ht : AlgebraicIndependent ℚ t) (κ : Derivation ℂ R (Q t i k))
    (v w : Derivation ℂ (P t i k) (Q t i k))
    (hvw : v (algebraMap ℂ[ε] (P t i k) ε) = w (algebraMap ℂ[ε] (P t i k) ε))
    (ω : Forms R 3) :
    mixed κ (v.compAlgebraMap R) ω = mixed κ (w.compAlgebraMap R) ω := by
  have := pair_formallySmooth t i k ht
  have := pair_exteriorTwo t i k ht
  exact mixed_eq_of_speed (algebraMap ℂ[ε] (P t i k) ε) (reduce_surjective t i k)
    (reduce_ker t i k) κ v w hvw ω

end CycleQ2LiteralThreefoldPairSpeed
end

#print axioms CycleQ2LiteralThreefoldPairSpeed.pair_speed
