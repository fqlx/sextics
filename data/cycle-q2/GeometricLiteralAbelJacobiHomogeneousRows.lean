import Proposal.GeometricLiteralAbelJacobiSectionRows
import Proposal.GeometricLiteralAbelJacobiProjectiveRestriction

/-!
# The global degree-fourteen numerator of each moving tangent row

Differentiating the coefficients of the relative section rows along the
original incidence tangent gives three weighted homogeneous polynomials.
Their dehomogenizations in every shifted affine chart are the tangent
rows computed from the actual moving curve equations. The three normal
values satisfy the degree-fourteen transition law on every pair of these charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2LiteralAbelJacobiHomogeneousRows

open MvPolynomial
open scoped DualNumber
open CycleQ2GeometricIncidenceProj CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartSeedFiber CycleQ2RelativeConstantSection
  CycleQ2IncidenceFirstOrder CycleQ2LiteralAbelJacobiSectionRows

private def coefficientTangent {σ : Type} (p : MvPolynomial σ ParameterAlgebra) : MvPolynomial σ ℂ :=
  AddMonoidAlgebra.map (seedMap.toAddMonoidHom.comp timeDerivation.toLinearMap.toAddMonoidHom) p

private theorem coefficientTangent_coeff {σ : Type} (p : MvPolynomial σ ParameterAlgebra) (m : σ →₀ ℕ) :
    coeff m (coefficientTangent p) = seedMap (timeDerivation (coeff m p)) := rfl

private theorem firstOrder_expansion {σ : Type} (p : MvPolynomial σ ParameterAlgebra) :
    MvPolynomial.map firstOrderMap.toRingHom p =
      MvPolynomial.map (algebraMap ℂ ℂ[ε]) (MvPolynomial.map seedMap p) +
        C ε * MvPolynomial.map (algebraMap ℂ ℂ[ε]) (coefficientTangent p) := by
  apply MvPolynomial.ext
  intro m
  simp only [coeff_add, coeff_C_mul, coeff_map, coefficientTangent_coeff]
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

private theorem dehomogenize_coefficientTangent (i : Fin 4) (p : MvPolynomial (Fin 5) ParameterAlgebra) :
    dehomogenize i (coefficientTangent p) = coefficientTangent (dehomogenize i p) := by
  have h := congrArg (dehomogenize (S := ℂ[ε]) i) (firstOrder_expansion p)
  rw [← map_dehomogenize, firstOrder_expansion, map_add, map_mul, MvPolynomial.algHom_C,
    ← map_dehomogenize, ← map_dehomogenize, ← map_dehomogenize] at h
  apply MvPolynomial.ext
  intro m
  have hm := congrArg (fun q : ChartPolynomial ℂ[ε] => (coeff m q).snd) h
  simpa [coeff_C_mul, coeff_map, TrivSqZeroExt.algebraMap_eq_inl] using hm.symm

/-- The derivative of the homogeneous relative row before choosing any weight-one chart. -/
def homogeneousTangentRow (t : Fin 3 → ℂ) (j : Fin 3) : MvPolynomial (Fin 5) ℂ :=
  coefficientTangent (relativeSectionPolynomial incidencePoint t j)

theorem homogeneousTangentRow_degree (t : Fin 3 → ℂ) (j : Fin 3) :
    (homogeneousTangentRow t j).IsWeightedHomogeneous geometricWeight 14 := by
  intro m hm
  apply (relativeSectionPolynomial_homogeneous incidencePoint t j)
  intro hz
  apply hm
  change seedMap (timeDerivation (coeff m (relativeSectionPolynomial incidencePoint t j))) = 0
  rw [hz, map_zero, map_zero]

theorem dehomogenize_homogeneousTangentRow (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3) :
    dehomogenize i (homogeneousTangentRow t j) = tangentRow t i j :=
  dehomogenize_coefficientTangent i (relativeSectionPolynomial incidencePoint t j)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiProjectiveRestriction

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.closedCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.closedAlgebra
  CycleQ2LiteralAbelJacobiProjectiveRestriction.coneCommRing

variable (t : Fin 3 → ℂ) (i j : Fin 4) (r : Fin 3)

/-- The actual velocity of the defining section row in the homogeneous coordinate chart. -/
def rowNormalValue [Module.Flat ℂ[ε] (B t i)] : ChartCone t i :=
  chartValue t i (chartNormal t i ((curveIdeal t i).toCotangent (rowEquation t i r)))

theorem rowNormalValue_mul_pow [Module.Flat ℂ[ε] (B t i)] :
    rowNormalValue t i r * algebraMap (Cone t) (ChartCone t i) (coord t i) ^ 14 =
      -algebraMap (Cone t) (ChartCone t i) (onCone t (homogeneousTangentRow t r)) := by
  rw [rowNormalValue, chartNormal_row, ← dehomogenize_homogeneousTangentRow, chartValue_neg, neg_mul]
  exact congrArg Neg.neg (chartValue_mul_pow t i 14 _ (homogeneousTangentRow_degree t r))

/-- All three actual degree-fourteen conormal generators have compatible normal values
in the original curve cone localized on both charts. -/
theorem rowNormalValue_overlap [Module.Flat ℂ[ε] (B t i)] [Module.Flat ℂ[ε] (B t j)] :
    fromFirst t i j (rowNormalValue t i r) * algebraMap (Cone t) (PairCone t i j) (coord t i) ^ 14 =
      fromSecond t i j (rowNormalValue t j r) * algebraMap (Cone t) (PairCone t i j) (coord t j) ^ 14 := by
  simp only [rowNormalValue, chartNormal_row, ← dehomogenize_homogeneousTangentRow, chartValue_neg,
    map_neg, neg_mul]
  exact congrArg Neg.neg (chartValue_overlap t i j 14 _ (homogeneousTangentRow_degree t r))

end CycleQ2LiteralAbelJacobiHomogeneousRows
end

#print axioms CycleQ2LiteralAbelJacobiHomogeneousRows.homogeneousTangentRow_degree
#print axioms CycleQ2LiteralAbelJacobiHomogeneousRows.dehomogenize_homogeneousTangentRow

#print axioms CycleQ2LiteralAbelJacobiHomogeneousRows.rowNormalValue_overlap
