import Proposal.GeometricLiteralCylinderPivot
import Proposal.GeometricLiteralAbelJacobiRelativeNormal
import Mathlib.RingTheory.Etale.Kaehler

/-!
# The localized deformation normal and the curve adjunction map

Localizing the intrinsic cubic contraction of the moving family produces
an endomorphism of the genuine curve differentials on each pivot open.
Composing that endomorphism with the curve adjunction map recovers the
determinant built from the original two moving equations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCylinderNormalComparison

open scoped TensorProduct DualNumber
open CycleQ2LiteralCylinderPivot CycleQ2CurveCylinderAdjunction CycleQ2CurveCylinderDifferential
  CycleQ2LiteralCylinderAdjunction CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiRelativeNormal
  CycleQ2LiteralAbelJacobiEquations CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralAbelJacobiSectionRows

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedTower
  CycleQ2LiteralCylinderPivot.curveOpenRing
  CycleQ2LiteralCylinderPivot.openCurveAlgebra
  CycleQ2LiteralCylinderPivot.localizedAlgebra
  CycleQ2LiteralCylinderPivot.localizedTower

variable (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart)
variable [Module.Flat ℂ[ε] (B t i)]

private abbrev seed := CycleQ2IncidencePolynomialJacobianBinding.seedPoint (57 : ℂ) Complex.I
private abbrev S := Submonoid.powers (CycleQ2LiteralAbelJacobiSeedLiftChart.toCurve seed t i p
  (CycleQ2LiteralAbelJacobiSeedLiftChart.rowPivot seed t i p))
private abbrev restrictForms := KaehlerDifferential.map ℂ ℂ (A t i) (CurveOpen t i p)

/-- Insert the intrinsic deformation normal into the fixed cubic conormal. -/
def cubicContraction : Module.End (A t i) (KaehlerDifferential ℂ (A t i)) :=
  relativeNormal t i ((idealOnT t i).toCotangent (cubicClass t i)) • LinearMap.id

theorem cubicContraction_apply (β : KaehlerDifferential ℂ (A t i)) :
    cubicContraction t i β = normalContraction (idealOnT t i) (relativeNormal t i)
      ((idealOnT t i).toCotangent (cubicClass t i) ⊗ₜ[T i] β) := rfl

/-- Localization of the actual affine deformation normal acting on curve forms. -/
def localizedContraction : Module.End (CurveOpen t i p) (KaehlerDifferential ℂ (CurveOpen t i p)) :=
  IsLocalizedModule.mapExtendScalars (S t i p) (restrictForms t i p) (restrictForms t i p)
    (CurveOpen t i p) (cubicContraction t i)

theorem localizedContraction_restrict (β : KaehlerDifferential ℂ (A t i)) :
    localizedContraction t i p (restrictForms t i p β) =
      restrictForms t i p (normalContraction (idealOnT t i) (relativeNormal t i)
        ((idealOnT t i).toCotangent (cubicClass t i) ⊗ₜ[T i] β)) :=
  IsLocalizedModule.map_apply (S t i p) (restrictForms t i p) (restrictForms t i p) (cubicContraction t i) β

/-- The localization formula also determines the contraction of forms with pivot denominators. -/
theorem localizedContraction_eq :
    localizedContraction t i p =
      -(algebraMap (A t i) (CurveOpen t i p) (seedChartMap t i (tangentL i))) • LinearMap.id := by
  apply LinearMap.restrictScalars_injective (A t i)
  apply IsLocalizedModule.linearMap_ext (S t i p) (restrictForms t i p) (restrictForms t i p)
  apply LinearMap.ext
  intro β
  change localizedContraction t i p (restrictForms t i p β) = -(algebraMap (A t i) (CurveOpen t i p)
    (seedChartMap t i (tangentL i))) • restrictForms t i p β
  rw [localizedContraction_restrict, relativeNormal_contraction, map_smul,
    ← (algebraMap (A t i) (CurveOpen t i p)).map_neg, IsScalarTower.algebraMap_smul]

set_option maxHeartbeats 1400000 in
/-- The mixed determinant for the two actual moving equations is precisely the
adjunction image of the original deformation normal, including on singular pivot charts. -/
theorem original_mixed_eq_normal_adjunction (β : OpenRestricted t i p) :
    let Q := FixedOpen i p
    let C := CurveOpen t i p
    let H := toOpen t i p (mixedMap i (KaehlerDifferential.D ℂ Parameters
      (dehomogenizedEquations incidencePoint i 1)))
    let G := toOpen t i p (mixedMap i (KaehlerDifferential.D ℂ Parameters (parameterRow t i p.1)))
    let h := algebraMap (T i) Q (cubicOnT i)
    adjunctionNumerator H G (exteriorPower.ιMulti C 2 ![((0, ambientD C h) : OpenTotal t i p), (0, β)]) =
      pivotAdjunction t i p (localizedContraction t i p (KaehlerDifferential.mapBaseChange ℂ Q C β)) := by
  dsimp only
  rw [original_mixed_on_differentials, localizedContraction_eq, LinearMap.smul_apply, LinearMap.id_apply,
    map_smul]

end CycleQ2LiteralCylinderNormalComparison
end

#print axioms CycleQ2LiteralCylinderNormalComparison.localizedContraction_restrict
#print axioms CycleQ2LiteralCylinderNormalComparison.original_mixed_eq_normal_adjunction
