import Proposal.GeometricLiteralAbelJacobiMovingNormal

/-!
# The cubic normal coefficient in the original projective overlaps

On each weight-one chart, evaluating the moving curve normal on the cubic
gives a degree-zero fraction. Multiplying by the cube of that chart's
homogeneous coordinate recovers the same signed homogeneous cubic on the
seed curve. The identities agree in the ring where both coordinates are units.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiProjectiveRestriction

open MvPolynomial HomogeneousLocalization
open scoped DualNumber
open CycleQ2GeometricIncidenceProj CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceDehomogenizedChart CycleQ2RelativeConstantSection
  CycleQ2RelativeConstantCurve CycleQ2RelativeCurveChart
  CycleQ2GradedLocalizationProjection CycleQ2IncidenceFirstOrderCanonicalH2
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiMovingNormal

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

private abbrev seed := seedPoint (57 : ℂ) Complex.I
variable (t : Fin 3 → ℂ) (i j : Fin 4)

abbrev Cone := RelativeCurveRing seed t
local instance coneCommRing : CommRing (Cone t) := inferInstance

/-- Image of an original homogeneous polynomial in the actual curve cone. -/
abbrev onCone (p : MvPolynomial (Fin 5) ℂ) : Cone t :=
  relativeCurveRingMap seed t (surfaceQuotient seed p)

abbrev coord := onCone t (X i.castSucc)
abbrev ChartCone := Localization.Away (coord t i)
abbrev PairCone := Localization.Away (coord t i * coord t j)

/-- Image of the original degree-zero affine curve chart in the localized cone. -/
def chartValue (u : A t i) : ChartCone t i :=
  ((curveCoordinateChartEquiv seed t i).symm u).val

theorem chartValue_neg (u : A t i) : chartValue t i (-u) = -chartValue t i u := by
  simp only [chartValue, map_neg, HomogeneousLocalization.val_neg]

/-- Clearing the chart denominator of any original homogeneous polynomial
recovers its image in the homogeneous curve quotient. -/
theorem chartValue_mul_pow (d : ℕ) (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous geometricWeight d) :
    chartValue t i (seedChartMap t i (dehomogenize i p)) *
      algebraMap (Cone t) (ChartCone t i) (coord t i) ^ d =
        algebraMap (Cone t) (ChartCone t i) (onCone t p) := by
  have hf : (curveCoordinateChartEquiv seed t i).symm (seedChartMap t i (dehomogenize i p)) =
      coordinateCurveMap seed t i (homogeneousFraction seed i d p hp) := by
    apply (curveCoordinateChartEquiv seed t i).injective
    rw [AlgEquiv.apply_symm_apply, curveCoordinateChartEquiv_map,
      familyCoordinateChartEquiv_homogeneousFraction]
    rfl
  rw [chartValue, hf]
  change (Away.map (relativeCurveRingMap seed t) _ (homogeneousFraction seed i d p hp)).val * _ = _
  simp only [homogeneousFraction, Away.map_mk, Away.val_mk, Localization.mk_eq_mk']
  let b := IsLocalization.mk' (ChartCone t i) (onCone t p) (powerDenominator (coord t i) d)
  change b * algebraMap (Cone t) (ChartCone t i) (coord t i) ^ d = _
  calc
    _ = b * algebraMap (Cone t) (ChartCone t i) (coord t i ^ d) :=
      congrArg (b * ·) (map_pow (algebraMap (Cone t) (ChartCone t i)) (coord t i) d).symm
    _ = _ := IsLocalization.mk'_spec (ChartCone t i) (onCone t p) (powerDenominator (coord t i) d)

/-- The value of the normal in the homogeneous coordinate trivialization. -/
def normalValue [Module.Flat ℂ[ε] (B t i)] : ChartCone t i :=
  chartValue t i (chartNormal t i ((curveIdeal t i).toCotangent (cubicEquation t i)))

theorem normalValue_mul_cube [Module.Flat ℂ[ε] (B t i)] :
    normalValue t i * algebraMap (Cone t) (ChartCone t i) (coord t i) ^ 3 =
      -algebraMap (Cone t) (ChartCone t i) (onCone t firstOrderWeightedCubic.val) := by
  rw [normalValue, chartNormal_H, chartValue_neg, neg_mul]
  exact congrArg Neg.neg (chartValue_mul_pow t i 3 firstOrderWeightedCubic.val firstOrderWeightedCubic.property)

def fromFirst : ChartCone t i →+* PairCone t i j :=
  IsLocalization.Away.awayToAwayRight (coord t i) (coord t j)

def fromSecond : ChartCone t j →+* PairCone t i j :=
  IsLocalization.Away.awayToAwayLeft (coord t j) (coord t i)

private theorem fromFirst_algebraMap (z : Cone t) :
    fromFirst t i j (algebraMap (Cone t) (ChartCone t i) z) =
      algebraMap (Cone t) (PairCone t i j) z :=
  IsLocalization.Away.awayToAwayRight_eq _ _ z

private theorem fromSecond_algebraMap (z : Cone t) :
    fromSecond t i j (algebraMap (Cone t) (ChartCone t j) z) =
      algebraMap (Cone t) (PairCone t i j) z :=
  IsLocalization.Away.awayToAwayLeft_eq _ _ z

/-- The degree-zero presentations of a homogeneous polynomial on any two
projective curve charts have one common numerator on the intersection. -/
theorem chartValue_overlap (d : ℕ) (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous geometricWeight d) :
    fromFirst t i j (chartValue t i (seedChartMap t i (dehomogenize i p))) *
        algebraMap (Cone t) (PairCone t i j) (coord t i) ^ d =
      fromSecond t i j (chartValue t j (seedChartMap t j (dehomogenize j p))) *
        algebraMap (Cone t) (PairCone t i j) (coord t j) ^ d := by
  have h₁ := congrArg (fromFirst t i j) (chartValue_mul_pow t i d p hp)
  have h₂ := congrArg (fromSecond t i j) (chartValue_mul_pow t j d p hp)
  simp only [map_mul, map_pow, fromFirst_algebraMap, fromSecond_algebraMap] at h₁ h₂
  exact h₁.trans h₂.symm

/-- The local normal evaluations satisfy the transition rule of the original
degree-three equation in the common localization of the curve cone. -/
theorem normalValue_overlap [Module.Flat ℂ[ε] (B t i)] [Module.Flat ℂ[ε] (B t j)] :
    fromFirst t i j (normalValue t i) * algebraMap (Cone t) (PairCone t i j) (coord t i) ^ 3 =
    fromSecond t i j (normalValue t j) * algebraMap (Cone t) (PairCone t i j) (coord t j) ^ 3 := by
  have h₁ := congrArg (fromFirst t i j) (normalValue_mul_cube t i)
  have h₂ := congrArg (fromSecond t i j) (normalValue_mul_cube t j)
  simp only [map_mul, map_pow, map_neg, fromFirst_algebraMap, fromSecond_algebraMap] at h₁ h₂
  exact h₁.trans h₂.symm

end CycleQ2LiteralAbelJacobiProjectiveRestriction
end

#print axioms CycleQ2LiteralAbelJacobiProjectiveRestriction.chartValue_overlap
#print axioms CycleQ2LiteralAbelJacobiProjectiveRestriction.normalValue_overlap
