import Proposal.GeometricLiteralThreefoldMovingVolume
import Proposal.GeometricThreefoldMixedCurveForm

/-!
# The canonical cubic one-form on the original moving curve

Contracting the oriented threefold volume by a surface tangent and the
moving ambient normal produces the negative contraction of the published
cubic two-form, as an equality in the curve's ordinary Kähler module.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

noncomputable section
namespace CycleQ2LiteralThreefoldMovingCurveForm

open scoped DualNumber
open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiRelativeNormal CycleQ2LiteralThreefoldSurfaceNormal
  CycleQ2LiteralThreefoldMovingVolume CycleQ2ThreefoldMixedCurveForm CycleQ2ThreefoldCurveEvaluation

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedTower
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralThreefoldSurfaceNormal.patchAlgebra
  CycleQ2LiteralThreefoldSurfaceNormal.patchTower
  CycleQ2LiteralThreefoldMovingVolume.curvePatchRing
  CycleQ2LiteralThreefoldMovingVolume.curveBaseAlgebra
  CycleQ2LiteralThreefoldMovingVolume.curveBaseSMul
  CycleQ2LiteralThreefoldMovingVolume.curveBaseModule
  CycleQ2LiteralThreefoldMovingVolume.curveComplexAlgebra
  CycleQ2LiteralThreefoldMovingVolume.curveComplexSMul
  CycleQ2LiteralThreefoldMovingVolume.curveComplexModule
  CycleQ2LiteralThreefoldMovingVolume.curveComplexTower
  CycleQ2LiteralThreefoldMovingVolume.surfaceAlgebra
  CycleQ2LiteralThreefoldMovingVolume.surfaceTower
  CycleQ2LiteralThreefoldMovingVolume.fixedAlgebra
  CycleQ2LiteralThreefoldMovingVolume.fixedSMul
  CycleQ2LiteralThreefoldMovingVolume.fixedModule
  CycleQ2LiteralThreefoldMovingVolume.fixedTower
  CycleQ2LiteralThreefoldMovingVolume.closedTower
  CycleQ2LiteralThreefoldMovingVolume.restrictionTower

variable (t : Fin 3 → ℂ) (j : Fin 3) (n a : P)

private theorem form_ext [Algebra.FormallySmooth ℂ (A t j.succ)]
    {α β : KaehlerDifferential ℂ (CurvePatch t j.succ n a)} (h : ∀ d : Derivation ℂ
      (CurvePatch t j.succ n a) (CurvePatch t j.succ n a), d.liftKaehlerDifferential α = d.liftKaehlerDifferential β) :
    α = β := by
  have : Algebra.FormallySmooth ℂ (CurvePatch t j.succ n a) :=
    Algebra.FormallySmooth.comp ℂ (A t j.succ) (CurvePatch t j.succ n a)
  exact curve_form_ext h

/-- The argument transverse to the cubic is retained in the ambient threefold
until both contractions have been taken. -/
theorem moving_mixed_form [Module.Flat ℂ[ε] (B t j.succ)] [Algebra.FormallySmooth ℂ (A t j.succ)]
    (v : Derivation ℂ (T j.succ) (A t j.succ))
    (hv : ∀ e : idealOnT t j.succ,
      v e.val = relativeNormal t j.succ ((idealOnT t j.succ).toCotangent e))
    (x : Derivation ℂ (Patch j.succ n a) (CurvePatch t j.succ n a)) :
    mixed (x.compAlgebraMap (T j.succ)) (restrictNormal t j.succ n a v) (orientedVolume j.succ) =
      -(contractRestrict x (orientedCubic n a j)) := by
  apply form_ext t j n a
  intro y
  rw [evaluate_mixed, map_neg, evaluate_contractRestrict]
  have h := moving_double_contraction t n a j v hv x (y.compAlgebraMap (Patch j.succ n a))
  rw [comp_tower (T := T j.succ) (U := Patch j.succ n a) y] at h
  exact h

/-- Every algebraically independent section has a single normal representative
on each weight-one chart giving the published signed one-form on every
Jacobian open of its original section curve. -/
theorem independent_mixed_form (ht : AlgebraicIndependent ℚ t) :
    ∃ v : Derivation ℂ (T j.succ) (A t j.succ), ∀ (n a : P)
      (x : Derivation ℂ (Patch j.succ n a) (CurvePatch t j.succ n a)),
      mixed (x.compAlgebraMap (T j.succ)) (restrictNormal t j.succ n a v) (orientedVolume j.succ) =
        -(contractRestrict x (orientedCubic n a j)) := by
  have hc := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  have hs := (CycleQ2LiteralAbelJacobiSeedLift.smooth_neighborhood_of_seed_minors t hc).1
  have := CycleQ2LiteralAbelJacobiSmoothNormal.flat_charts_of_smooth t hs j.succ
  have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t hc j.succ
  obtain ⟨v,hv,_⟩ := exists_moving_representative t j.succ
  exact ⟨v, fun n a => moving_mixed_form t j n a v hv⟩

end CycleQ2LiteralThreefoldMovingCurveForm
end

#print axioms CycleQ2LiteralThreefoldMovingCurveForm.moving_mixed_form
#print axioms CycleQ2LiteralThreefoldMovingCurveForm.independent_mixed_form
