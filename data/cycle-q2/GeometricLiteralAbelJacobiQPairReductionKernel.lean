import Proposal.GeometricLiteralAbelJacobiQPairReduction
import Proposal.GeometricFirstOrderLocalizedReduction

/-!
# The actual closed fibre of the two-chart germ

Quotienting by the original dual-number parameter commutes with inversion
of the second weight-one coordinate. The resulting quotient isomorphism
induces the pair-ring reduction used by the cylinder test form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiQPairReductionKernel

open scoped DualNumber
open CycleQ2LiteralAbelJacobiQPairCharts CycleQ2LiteralAbelJacobiQPairReduction
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralCylinderEvaluation CycleQ2DualNumberRegularQuotient
  CycleQ2FirstOrderLocalizedReduction CycleQ2FirstOrderChartReduction

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower

variable (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3)

private theorem denominator_reduces :
    curveChartReductionEquiv t i (Ideal.Quotient.mk _ (movingMap t i (ratio i k))) =
      toCurve t i (ratio i k) :=
  (IsScalarTower.algebraMap_apply (T i) (B t i) (A t i) (ratio i k)).symm

/-- Reduction of the pair modulo its original parameter is the actual closed pair ring. -/
def fibreEquiv : (BPair t i k ⧸ epsilonIdeal (k := ℂ) (BPair t i k)) ≃+* APair t i k :=
  localizedReductionEquiv (movingMap t i (ratio i k)) (curveChartReductionEquiv t i) _
    (denominator_reduces t i k)

theorem fibreEquiv_mk : (fibreEquiv t i k).toRingHom.comp (Ideal.Quotient.mk _) = (reduce t i k).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (movingMap t i (ratio i k)))
  apply RingHom.ext
  intro b
  change fibreEquiv t i k (Ideal.Quotient.mk _ (algebraMap (B t i) (BPair t i k) b)) =
    reduce t i k (algebraMap (B t i) (BPair t i k) b)
  rw [reduce_localize]
  exact localizedReductionEquiv_mk _ b (curveChartReductionEquiv t i) _ (denominator_reduces t i k)

theorem reduce_surjective : Function.Surjective (reduce t i k) := by
  change Function.Surjective (reduce t i k).toRingHom
  rw [← fibreEquiv_mk]
  exact (fibreEquiv t i k).surjective.comp Ideal.Quotient.mk_surjective

theorem reduce_ker : RingHom.ker (reduce t i k).toRingHom = epsilonIdeal (k := ℂ) (BPair t i k) := by
  rw [← fibreEquiv_mk]
  ext b
  change fibreEquiv t i k (Ideal.Quotient.mk _ b) = 0 ↔ b ∈ _
  rw [map_eq_zero_iff _ (fibreEquiv t i k).injective, Ideal.Quotient.eq_zero_iff_mem]

end CycleQ2LiteralAbelJacobiQPairReductionKernel
end

#print axioms CycleQ2LiteralAbelJacobiQPairReductionKernel.reduce_ker
#print axioms CycleQ2LiteralAbelJacobiQPairReductionKernel.reduce_surjective

