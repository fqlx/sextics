import Proposal.GeometricLiteralAbelJacobiMovingNormal
import Proposal.GeometricFirstOrderLocalizedReduction
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Algebra

/-!
# Restricting the moving normal to principal chart refinements

The normal obtained by dividing by the original infinitesimal parameter on a
localized curve chart is the restriction of the original chart normal. The
comparison acts on every conormal class and uses the actual localized closed
curve and its original cubic equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiRestrictions

open scoped DualNumber
open CycleQ2DualNumberRegularQuotient CycleQ2FirstOrderChartReduction
  CycleQ2FirstOrderLocalizedReduction CycleQ2LiteralAbelJacobiNormal
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiMovingNormal

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.closedCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.thickAlgebra
  CycleQ2LiteralAbelJacobiMovingNormal.closedAlgebra

variable (t : Fin 3 → ℂ) (i : Fin 4) (g : P)

abbrev Ambient (g : P) := Localization.Away g
abbrev Thick := Localization.Away (chartMap t i g : B t i)
abbrev Closed := Localization.Away (seedChartMap t i g : A t i)

local instance thickRing : CommRing (Thick t i g) := inferInstance
local instance closedRing : CommRing (Closed t i g) := inferInstance
local instance thickBaseAlg : Algebra (B t i) (Thick t i g) := inferInstance
local instance closedBaseAlg : Algebra (A t i) (Closed t i g) := inferInstance
local instance thickDual : Algebra ℂ[ε] (Thick t i g) := inferInstance
local instance thickFlat [Module.Flat ℂ[ε] (B t i)] : Module.Flat ℂ[ε] (Thick t i g) :=
  Localization.flat (B t i) (Submonoid.powers (chartMap t i g : B t i))

def thickMap : Ambient g →+* Thick t i g :=
  IsLocalization.Away.map (R := P) (P := B t i) (Ambient g) (Thick t i g) (chartMap t i) g

def closedMap : Ambient g →+* Closed t i g :=
  IsLocalization.Away.map (R := P) (P := A t i) (Ambient g) (Closed t i g) (seedChartMap t i) g

local instance thickLocalizedAlgebra : Algebra (Ambient g) (Thick t i g) := (thickMap t i g).toAlgebra
local instance closedLocalizedAlgebra : Algebra (Ambient g) (Closed t i g) := (closedMap t i g).toAlgebra

private theorem thickMap_mk (p : P) :
    thickMap t i g (algebraMap P (Ambient g) p) =
      algebraMap (B t i) (Thick t i g) (chartMap t i p) := by
  simp only [thickMap, IsLocalization.Away.map, IsLocalization.map_eq]

private theorem closedMap_mk (p : P) :
    closedMap t i g (algebraMap P (Ambient g) p) =
      algebraMap (A t i) (Closed t i g) (seedChartMap t i p) := by
  simp only [closedMap, IsLocalization.Away.map, IsLocalization.map_eq]

/-- The closed fiber on this principal open of the original chart. -/
def reduction : ((Thick t i g) ⧸ epsilonIdeal (k := ℂ) (Thick t i g)) ≃+* Closed t i g :=
  localizedReductionEquiv (chartMap t i g) (curveChartReductionEquiv t i) (seedChartMap t i g)
    (chartMap_reduction t i g)

private theorem reduction_mk (b : B t i) :
    reduction t i g (Ideal.Quotient.mk _ (algebraMap (B t i) (Thick t i g) b)) =
      algebraMap (A t i) (Closed t i g) (curveChartReductionEquiv t i (Ideal.Quotient.mk _ b)) :=
  localizedReductionEquiv_mk _ _ _ _ _

theorem reduction_polynomial (x : Ambient g) :
    reduction t i g (Ideal.Quotient.mk _ (thickMap t i g x)) = closedMap t i g x := by
  have eqn : (reduction t i g).toRingHom.comp ((Ideal.Quotient.mk _).comp (thickMap t i g)) =
      closedMap t i g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      thickMap_mk, closedMap_mk, reduction_mk, chartMap_reduction]
  exact RingHom.congr_fun eqn x

abbrev refinedIdeal := RingHom.ker (closedMap t i g)

theorem refinedIdeal_eq_map :
    refinedIdeal t i g = (curveIdeal t i).map (algebraMap P (Ambient g)) :=
  IsLocalization.ker_map (S := Ambient g) (Closed t i g) (seedChartMap t i)
    (Submonoid.map_powers (seedChartMap t i) g)

private theorem refined_le_comap : refinedIdeal t i g ≤ closedIdeal (k := ℂ) (Thick t i g) (Ambient g) := by
  intro x hx
  change thickMap t i g x ∈ epsilonIdeal (k := ℂ) (Thick t i g)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (reduction t i g).injective
  rw [map_zero]
  exact (reduction_polynomial t i g x).trans hx

private def reductionLinear : ((Thick t i g) ⧸ epsilonIdeal (k := ℂ) (Thick t i g)) →ₗ[Ambient g] Closed t i g where
  toFun := reduction t i g
  map_add' := (reduction t i g).map_add
  map_smul' r x := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    change reduction t i g (Ideal.Quotient.mk _ (thickMap t i g r * b)) =
      closedMap t i g r * reduction t i g (Ideal.Quotient.mk _ b)
    rw [map_mul, map_mul, reduction_polynomial]

/-- The conormal functional computed inside the localized first-order curve. -/
def refinedNormal [Module.Flat ℂ[ε] (B t i)] :
    (refinedIdeal t i g).Cotangent →ₗ[Ambient g] Closed t i g :=
  (reductionLinear t i g).comp ((normal (k := ℂ) (Thick t i g) (Ambient g)).comp
    (Ideal.mapCotangent _ _ (AlgHom.id _ _) (refined_le_comap t i g)))

private theorem refinedNormal_lift [Module.Flat ℂ[ε] (B t i)] (p : refinedIdeal t i g)
    (b : Thick t i g) (h : thickMap t i g p = algebraMap ℂ[ε] (Thick t i g) ε * b) :
    refinedNormal t i g ((refinedIdeal t i g).toCotangent p) = reduction t i g (Ideal.Quotient.mk _ b) :=
  congrArg (reduction t i g) (normal_on_lift (k := ℂ) (Thick t i g) (Ambient g)
    ⟨p, refined_le_comap t i g p.property⟩ b h)

private theorem ideal_restrict : curveIdeal t i ≤ (refinedIdeal t i g).comap (algebraMap P (Ambient g)) := by
  intro p hp
  change closedMap t i g (algebraMap P (Ambient g) p) = 0
  rw [closedMap_mk, show seedChartMap t i p = 0 from hp, map_zero]

/-- Restriction on conormal modules along the original ambient localization. -/
def conormalRestrict : (curveIdeal t i).Cotangent →ₗ[P] (refinedIdeal t i g).Cotangent :=
  Ideal.mapCotangent _ _ (Algebra.ofId P (Ambient g)) (ideal_restrict t i g)

/-- Every localized conormal class comes from the original chart after clearing a denominator. -/
theorem conormalRestrict_clear (w : (refinedIdeal t i g).Cotangent) :
    ∃ d : Submonoid.powers g, ∃ v : (curveIdeal t i).Cotangent,
      algebraMap P (Ambient g) d • w = conormalRestrict t i g v := by
  obtain ⟨p, rfl⟩ := (refinedIdeal t i g).toCotangent_surjective w
  have hp := (le_of_eq (refinedIdeal_eq_map t i g)) p.property
  obtain ⟨⟨q, d⟩, hd⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) (Ambient g)).mp hp
  refine ⟨d, (curveIdeal t i).toCotangent q, ?_⟩
  rw [← map_smul]
  apply congrArg (refinedIdeal t i g).toCotangent
  apply Subtype.ext
  change algebraMap P (Ambient g) d * p.val = algebraMap P (Ambient g) q.val
  exact (mul_comm _ _).trans hd

/-- Division by the original epsilon commutes with restriction on every conormal class. -/
theorem refinedNormal_restrict [Module.Flat ℂ[ε] (B t i)] (v : (curveIdeal t i).Cotangent) :
    refinedNormal t i g (conormalRestrict t i g v) =
      algebraMap (A t i) (Closed t i g) (chartNormal t i v) := by
  obtain ⟨p, rfl⟩ := (curveIdeal t i).toCotangent_surjective v
  have hp : chartMap t i p ∈ epsilonIdeal (k := ℂ) (B t i) := curveIdeal_le_comap t i p.property
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hp
  let q : refinedIdeal t i g := ⟨algebraMap P (Ambient g) p, ideal_restrict t i g p.property⟩
  change refinedNormal t i g ((refinedIdeal t i g).toCotangent q) = _
  have hq : thickMap t i g q = algebraMap ℂ[ε] (Thick t i g) ε * algebraMap (B t i) (Thick t i g) b := by
    change thickMap t i g (algebraMap P (Ambient g) p) = _
    rw [thickMap_mk, show chartMap t i p = algebraMap ℂ[ε] (B t i) ε * b from hb,
      map_mul, ← IsScalarTower.algebraMap_apply ℂ[ε] (B t i) (Thick t i g)]
  rw [refinedNormal_lift t i g q _ hq, reduction_mk, chartNormal_lift t i p b hb]

/-- The original normal functional uniquely determines the independently computed localized one. -/
theorem refinedNormal_unique [Module.Flat ℂ[ε] (B t i)]
    (ν : (refinedIdeal t i g).Cotangent →ₗ[Ambient g] Closed t i g)
    (hν : ∀ v, ν (conormalRestrict t i g v) =
      algebraMap (A t i) (Closed t i g) (chartNormal t i v)) : ν = refinedNormal t i g := by
  apply LinearMap.ext
  intro w
  obtain ⟨d, v, hd⟩ := conormalRestrict_clear t i g w
  apply ((IsLocalization.map_units (Ambient g) d).map (closedMap t i g)).mul_right_injective
  change algebraMap P (Ambient g) d • ν w = algebraMap P (Ambient g) d • refinedNormal t i g w
  rw [← map_smul, ← map_smul, hd, hν, refinedNormal_restrict]

theorem refinedNormal_cubic [Module.Flat ℂ[ε] (B t i)] :
    refinedNormal t i g (conormalRestrict t i g ((curveIdeal t i).toCotangent (cubicEquation t i))) =
      -(closedMap t i g (algebraMap P (Ambient g) (tangentL i))) := by
  rw [refinedNormal_restrict, chartNormal_H, map_neg, closedMap_mk]

end CycleQ2LiteralAbelJacobiRestrictions
end

#print axioms CycleQ2LiteralAbelJacobiRestrictions.refinedNormal_unique
#print axioms CycleQ2LiteralAbelJacobiRestrictions.refinedNormal_restrict
#print axioms CycleQ2LiteralAbelJacobiRestrictions.refinedNormal_cubic
