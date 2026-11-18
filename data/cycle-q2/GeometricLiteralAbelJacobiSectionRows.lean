import Proposal.GeometricLiteralAbelJacobiMovingNormal

/-!
# The normal values of the three moving degree-fourteen section rows

The three equations of the original relative curve differentiate coefficient
by coefficient along its specified incidence parameter. Their classes in the
embedded conormal module have normal value minus their differentiated rows,
restricted to the original complex curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSectionRows

open MvPolynomial
open scoped DualNumber TensorProduct
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartSeedFiber CycleQ2RelativeCurveChart CycleQ2RelativeConstantSection
  CycleQ2IncidenceFirstOrder CycleQ2FirstOrderChartReduction
  CycleQ2LiteralAbelJacobiEquations

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower

variable (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3)

def parameterRow : ChartPolynomial ParameterAlgebra :=
  dehomogenize i (relativeSectionPolynomial incidencePoint t j)

def seedRow : ChartPolynomial ℂ :=
  dehomogenize i (relativeSectionPolynomial (seedPoint (57 : ℂ) Complex.I) t j)

/-- The original time derivation acts on every coefficient of the relative row
before evaluation at the distinguished point. -/
def tangentRow : ChartPolynomial ℂ :=
  AddMonoidAlgebra.map (seedMap.toAddMonoidHom.comp timeDerivation.toLinearMap.toAddMonoidHom)
    (parameterRow t i j)

theorem tangentRow_coeff (m : Option (Fin 3) →₀ ℕ) :
    coeff m (tangentRow t i j) = seedMap (timeDerivation (coeff m (parameterRow t i j))) := rfl

theorem parameterRow_seed : MvPolynomial.map seedMap (parameterRow t i j) = seedRow t i j := by
  rw [parameterRow, map_dehomogenize, relativeSectionPolynomial_seed]
  rfl

theorem parameterRow_firstOrder :
    MvPolynomial.map firstOrderMap.toRingHom (parameterRow t i j) =
      MvPolynomial.map (algebraMap ℂ ℂ[ε]) (seedRow t i j) +
        C ε * MvPolynomial.map (algebraMap ℂ ℂ[ε]) (tangentRow t i j) := by
  rw [← parameterRow_seed t i j]
  apply MvPolynomial.ext
  intro m
  simp only [coeff_add, coeff_C_mul, coeff_map, tangentRow_coeff]
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

private theorem parameterRow_zero : relativeEval t i (parameterRow t i j) = 0 := by
  have h : Ideal.Quotient.mk (affineSectionIdeal incidencePoint t i)
      (affineSectionEquation incidencePoint t i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  change Algebra.TensorProduct.includeRight (R := ParameterAlgebra) (A := ℂ[ε])
    (B := AffineCurveChart incidencePoint t i) (Ideal.Quotient.mk _
      (affineSectionEquation incidencePoint t i j)) = 0
  rw [h, map_zero]

theorem chartMap_seedRow : chartMap t i (seedRow t i j) =
    -(algebraMap ℂ[ε] (FirstOrderCurveChart t i) ε * chartMap t i (tangentRow t i j)) := by
  have h := parameterRow_zero t i j
  rw [← dualEval_parameter, parameterRow_firstOrder, map_add, map_mul, dualEval_constant,
    dualEval_constant, show dualEval t i (C ε) = _ from eval₂Hom_C _ _ _] at h
  exact eq_neg_of_add_eq_zero_left h

open CycleQ2LiteralAbelJacobiMovingNormal

attribute [local instance] CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.closedCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.closedAlgebra

/-- A degree-fourteen row as an element of the actual embedded curve ideal. -/
def rowEquation : curveIdeal t i := ⟨seedRow t i j,
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)⟩

theorem chartNormal_row [Module.Flat ℂ[ε] (B t i)] :
    chartNormal t i ((curveIdeal t i).toCotangent (rowEquation t i j)) =
      -(seedChartMap t i (tangentRow t i j)) := by
  let b : B t i := chartMap t i (tangentRow t i j)
  have h : chartMap t i (rowEquation t i j).val = algebraMap ℂ[ε] (B t i) ε * -b := by
    change chartMap t i (seedRow t i j) = _
    exact (chartMap_seedRow t i j).trans (mul_neg (algebraMap ℂ[ε] (B t i) ε) b).symm
  exact (chartNormal_lift t i (rowEquation t i j) (-b) h).trans (by
    rw [map_neg, map_neg, chartMap_reduction])

/-- The two original surface equations and the three moving rows generate the
whole ambient ideal of the original embedded seed curve. -/
theorem curveIdeal_span : curveIdeal t i = Ideal.span
    (Set.range (dehomogenizedEquations (seedPoint (57 : ℂ) Complex.I) i) ∪
      Set.range (seedRow t i)) := by
  let seed := seedPoint (57 : ℂ) Complex.I
  let f := dehomogenizedMap seed i
  have hker : curveIdeal t i = (affineSectionIdeal seed t i).comap f := by
    ext p
    exact Ideal.Quotient.eq_zero_iff_mem
  have hrows : (Ideal.span (Set.range (seedRow t i))).map f = affineSectionIdeal seed t i := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hker, ← hrows, Ideal.comap_map_of_surjective' f Ideal.Quotient.mk_surjective,
    Ideal.span_union, sup_comm]
  exact congrArg (fun I => I ⊔ Ideal.span (Set.range (seedRow t i))) Ideal.mk_ker

/-- Agreement on these five concrete equations determines the entire normal functional. -/
theorem normal_ext (ν μ : (curveIdeal t i).Cotangent →ₗ[P] A t i)
    (hF : ν ((curveIdeal t i).toCotangent (sexticEquation t i)) =
      μ ((curveIdeal t i).toCotangent (sexticEquation t i)))
    (hH : ν ((curveIdeal t i).toCotangent (cubicEquation t i)) =
      μ ((curveIdeal t i).toCotangent (cubicEquation t i)))
    (hrows : ∀ j : Fin 3, ν ((curveIdeal t i).toCotangent (rowEquation t i j)) =
      μ ((curveIdeal t i).toCotangent (rowEquation t i j))) : ν = μ := by
  let n := (ν - μ).comp (curveIdeal t i).toCotangent
  have h : curveIdeal t i ≤ n.ker.map (curveIdeal t i).subtype := by
    conv_lhs => rw [curveIdeal_span]
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · fin_cases k
      · exact ⟨sexticEquation t i, sub_eq_zero.mpr hF, rfl⟩
      · exact ⟨cubicEquation t i, sub_eq_zero.mpr hH, rfl⟩
    · exact ⟨rowEquation t i k, sub_eq_zero.mpr (hrows k), rfl⟩
  apply LinearMap.ext
  intro e
  obtain ⟨x, rfl⟩ := (curveIdeal t i).toCotangent_surjective e
  obtain ⟨z, hz, hzx⟩ := h x.property
  have hzx' : z = x := Subtype.ext hzx
  subst z
  exact sub_eq_zero.mp hz

/-- One nonzero coefficient vector works simultaneously on all four original charts.
The five computed normal values uniquely specify the motion on each chart. -/
theorem exists_unique_moving_normal :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧ ∀ i : Fin 4,
      ∃! ν : (curveIdeal t i).Cotangent →ₗ[P] A t i,
        ν ((curveIdeal t i).toCotangent (sexticEquation t i)) = 0 ∧
        ν ((curveIdeal t i).toCotangent (cubicEquation t i)) =
          -(seedChartMap t i (tangentL i)) ∧
        ∀ j : Fin 3, ν ((curveIdeal t i).toCotangent (rowEquation t i j)) =
          -(seedChartMap t i (tangentRow t i j)) := by
  obtain ⟨t, ht, hflat⟩ :=
    CycleQ2FirstOrderCurvePivotCover.exists_nonzero_firstOrderCurveCharts_flat
  refine ⟨t, ht, fun i => ?_⟩
  let := hflat i
  refine ⟨chartNormal t i, ⟨chartNormal_F t i, chartNormal_H t i, fun j => chartNormal_row t i j⟩, ?_⟩
  rintro ν ⟨hF, hH, hrows⟩
  exact normal_ext t i ν (chartNormal t i) (hF.trans (chartNormal_F t i).symm)
    (hH.trans (chartNormal_H t i).symm) (fun j => (hrows j).trans (chartNormal_row t i j).symm)

end CycleQ2LiteralAbelJacobiSectionRows
end

#print axioms CycleQ2LiteralAbelJacobiSectionRows.chartNormal_row
#print axioms CycleQ2LiteralAbelJacobiSectionRows.exists_unique_moving_normal
