import Proposal.GeometricCurveCylinderAdjunction
import Proposal.GeometricLiteralAbelJacobiSectionRows
import Proposal.GeometricLiteralAbelJacobiContraction

/-!
# Differentials of the original cubic and section equations at first order

For a polynomial on the parameter chart, differentiate its coefficients along
the retained time derivation and its closed specialization in the fixed
threefold coordinates. These are the parameter and fibre components of its
total differential along the fixed threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCylinderAdjunction

open MvPolynomial
open scoped DualNumber TensorProduct
open CycleQ2CurveCylinderAdjunction CycleQ2GeometricIncidenceProj
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceEtaleParameter
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartSeedFiber CycleQ2IncidenceFirstOrder CycleQ2FirstOrderChartReduction
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiSectionRows
  CycleQ2PolynomialCoefficientDerivation

abbrev Parameters := ChartPolynomial ParameterAlgebra
local instance parameterRing : CommRing Parameters := inferInstance
local instance threefoldRing (i : Fin 4) : CommRing (T i) := inferInstance

/-- Evaluation at the closed parameter in the original fixed threefold chart. -/
def evaluate (i : Fin 4) : Parameters →+* T i :=
  (Ideal.Quotient.mk (fixedIdeal i)).comp (MvPolynomial.map seedMap)

local instance parameterAlgebra (i : Fin 4) : Algebra Parameters (T i) := (evaluate i).toAlgebra

local instance parameterTower (i : Fin 4) : IsScalarTower ℂ Parameters (T i) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change Ideal.Quotient.mk _ (C c) = Ideal.Quotient.mk _ ((MvPolynomial.map seedMap) (C _))
    rw [MvPolynomial.map_C, CycleQ2IncidenceSeedFiber.seedMap_complex]

/-- The two components of the actual Kähler differential on the parameter
chart, evaluated in the fixed threefold coordinates. -/
def mixed (i : Fin 4) (p : Parameters) : T i × KaehlerDifferential ℂ (T i) :=
  (evaluate i (coefficientDerivation timeDerivation p), KaehlerDifferential.D ℂ (T i) (evaluate i p))

/-- The mixed differential factors through the universal Kähler differential
of the parameter chart, using the coefficient derivation for its first slot. -/
def mixedMap (i : Fin 4) : KaehlerDifferential ℂ Parameters →ₗ[Parameters]
    (T i × KaehlerDifferential ℂ (T i)) :=
  ((Algebra.linearMap Parameters (T i)).comp
    (coefficientDerivation (σ := Option (Fin 3)) timeDerivation).liftKaehlerDifferential).prod
    (KaehlerDifferential.map ℂ ℂ Parameters (T i))

theorem mixedMap_D (i : Fin 4) (p : Parameters) :
    mixedMap i (KaehlerDifferential.D ℂ Parameters p) = mixed i p := by
  apply Prod.ext
  · change algebraMap Parameters (T i) ((coefficientDerivation timeDerivation).liftKaehlerDifferential
        (KaehlerDifferential.D ℂ Parameters p)) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl
  · exact KaehlerDifferential.map_D ℂ ℂ Parameters (T i) p

private theorem coefficient_time (p : Parameters) (m : Option (Fin 3) →₀ ℕ) :
    coeff m (coefficientDerivation timeDerivation p) = timeDerivation (coeff m p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [coefficientDerivation_monomial]
    by_cases h : e = m <;> simp [MvPolynomial.coeff_monomial, h]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, map_add, hp, hq]

private theorem components_of_expansion (p : Parameters) (p₀ p₁ : P)
    (h : MvPolynomial.map firstOrderMap.toRingHom p =
      MvPolynomial.map (algebraMap ℂ ℂ[ε]) p₀ + C ε * MvPolynomial.map (algebraMap ℂ ℂ[ε]) p₁) :
    MvPolynomial.map seedMap p = p₀ ∧
      MvPolynomial.map seedMap (coefficientDerivation timeDerivation p) = p₁ := by
  constructor
  · ext m
    have hm := congrArg (fun q : ChartPolynomial ℂ[ε] => (coeff m q).fst) h
    simpa [coeff_add, coeff_C_mul, coeff_map, TrivSqZeroExt.algebraMap_eq_inl] using hm
  · ext m
    have hm := congrArg (fun q : ChartPolynomial ℂ[ε] => (coeff m q).snd) h
    simpa [coeff_add, coeff_C_mul, coeff_map, coefficient_time,
      TrivSqZeroExt.snd_mul, TrivSqZeroExt.algebraMap_eq_inl] using hm

theorem mixed_of_expansion (i : Fin 4) (p : Parameters) (p₀ p₁ : P)
    (h : MvPolynomial.map firstOrderMap.toRingHom p =
      MvPolynomial.map (algebraMap ℂ ℂ[ε]) p₀ + C ε * MvPolynomial.map (algebraMap ℂ ℂ[ε]) p₁) :
    mixed i p = (Ideal.Quotient.mk _ p₁, KaehlerDifferential.D ℂ (T i) (Ideal.Quotient.mk _ p₀)) := by
  obtain ⟨h₀, h₁⟩ := components_of_expansion p p₀ p₁ h
  simp only [mixed, evaluate, RingHom.comp_apply, h₀, h₁]

/-- Reduced total differential of the actual moving degree-fourteen row. -/
theorem mixed_row (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3) :
    mixed i (parameterRow t i j) =
      (Ideal.Quotient.mk (fixedIdeal i) (tangentRow t i j),
        KaehlerDifferential.D ℂ (T i) (Ideal.Quotient.mk _ (seedRow t i j))) :=
  mixed_of_expansion i _ _ _ (parameterRow_firstOrder t i j)

/-- The actual first-order parameter polynomial of the cubic on a fixed chart. -/
theorem parameterCubic_firstOrder (i : Fin 4) :
    MvPolynomial.map firstOrderMap.toRingHom (dehomogenizedEquations incidencePoint i 1) =
      MvPolynomial.map (algebraMap ℂ ℂ[ε]) (seedH i) +
        C ε * MvPolynomial.map (algebraMap ℂ ℂ[ε]) (tangentL i) := by
  change MvPolynomial.map _ (dehomogenize i (pointEquationH incidencePoint)) = _
  rw [map_dehomogenize, cubic_coefficients, map_add, map_mul,
    ← map_dehomogenize, ← map_dehomogenize, MvPolynomial.algHom_C]
  rfl

theorem mixed_cubic (i : Fin 4) :
    mixed i (dehomogenizedEquations incidencePoint i 1) =
      (Ideal.Quotient.mk (fixedIdeal i) (tangentL i), KaehlerDifferential.D ℂ (T i) (cubicOnT i)) :=
  mixed_of_expansion i _ _ _ (parameterCubic_firstOrder i)

abbrev MixedForms (i : Fin 4) := T i × KaehlerDifferential ℂ (T i)

def dt (i : Fin 4) : MixedForms i := (1, 0)

def vertical (i : Fin 4) (β : KaehlerDifferential ℂ (T i)) : MixedForms i := (0, β)

def verticalCubic (i : Fin 4) := vertical i (KaehlerDifferential.D ℂ (T i) (cubicOnT i))

def verticalRow (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3) :=
  vertical i (KaehlerDifferential.D ℂ (T i) (Ideal.Quotient.mk _ (seedRow t i j)))

private theorem splitPair (i : Fin 4) (p : T i) (β : KaehlerDifferential ℂ (T i)) :
    ((p, β) : MixedForms i) = vertical i β + p • dt i := by
  ext <;> simp [vertical, dt]

theorem moving_cubic_differential (i : Fin 4) :
    mixedMap i (KaehlerDifferential.D ℂ Parameters (dehomogenizedEquations incidencePoint i 1)) =
      verticalCubic i + (Ideal.Quotient.mk (fixedIdeal i) (tangentL i)) • dt i :=
  (mixedMap_D _ _).trans ((mixed_cubic _).trans (splitPair _ _ _))

theorem moving_row_differential (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3) :
    mixedMap i (KaehlerDifferential.D ℂ Parameters (parameterRow t i j)) =
      verticalRow t i j + (Ideal.Quotient.mk (fixedIdeal i) (tangentRow t i j)) • dt i :=
  (mixedMap_D _ _).trans ((mixed_row _ _ _).trans (splitPair _ _ _))

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
local instance seedRing (t : Fin 3 → ℂ) (i : Fin 4) : CommRing (A t i) := inferInstance

abbrev SeedMixed (t : Fin 3 → ℂ) (i : Fin 4) := A t i ⊗[T i] MixedForms i

/-- Restriction of fixed-chart covectors to the original closed curve. -/
def restrictMixed (t : Fin 3 → ℂ) (i : Fin 4) : MixedForms i →ₗ[T i] SeedMixed t i :=
  TensorProduct.mk (T i) (A t i) (MixedForms i) 1

private theorem restrictMixed_smul (t : Fin 3 → ℂ) (i : Fin 4) (p : P) (β : MixedForms i) :
    restrictMixed t i ((Ideal.Quotient.mk (fixedIdeal i) p) • β) =
      seedChartMap t i p • restrictMixed t i β := by
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul (A t i) _ _).symm

/-- On each original closed curve chart, with any of the three moving rows,
the normalized adjunction expression is independent of that row's velocity.
On a principal pivot where the row cuts the Cartier curve this is its local
complete-intersection numerator. -/
theorem moving_curve_adjunction (t : Fin 3 → ℂ) (i : Fin 4) (j : Fin 3)
    (β : SeedMixed t i) :
    let s := restrictMixed t i
    let H := mixedMap i (KaehlerDifferential.D ℂ Parameters (dehomogenizedEquations incidencePoint i 1))
    let G := mixedMap i (KaehlerDifferential.D ℂ Parameters (parameterRow t i j))
    adjunctionNumerator (s H) (s G) (exteriorPower.ιMulti (A t i) 2 ![s (verticalCubic i), β]) =
      -(seedChartMap t i (tangentL i)) • fibreNumerator (R := A t i)
        (s (dt i)) (s (verticalCubic i)) (s (verticalRow t i j))
        ((fibreConormals (R := A t i) (s (dt i)) (s (verticalCubic i)) (s (verticalRow t i j))).mkQ β) := by
  dsimp only
  rw [moving_cubic_differential, moving_row_differential, map_add, map_add,
    restrictMixed_smul, restrictMixed_smul]
  exact moving_conormal_on_fibre _ _ _ _ _ _

end CycleQ2LiteralCylinderAdjunction
end

#print axioms CycleQ2LiteralCylinderAdjunction.mixed_row

#print axioms CycleQ2LiteralCylinderAdjunction.moving_cubic_differential
#print axioms CycleQ2LiteralCylinderAdjunction.moving_row_differential

#print axioms CycleQ2LiteralCylinderAdjunction.moving_curve_adjunction
