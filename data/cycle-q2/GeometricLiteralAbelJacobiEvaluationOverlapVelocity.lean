import Proposal.GeometricLiteralCylinderEvaluation

/-!
# Restricting chart velocities to the same affine overlap

Extension through the differential map of an affine open immersion gives
a restricted chart velocity with coefficients in the closed fibre. For an
affine subopen of two original curve charts, the two restricted velocities
therefore induce the same evaluation of all family two-forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationOverlapVelocity

open CategoryTheory AlgebraicGeometry
open scoped DualNumber TensorProduct
open CycleQ2DualNumberRegularQuotient CycleQ2CurveParameterTangent
  CycleQ2LiteralAbelJacobiContraction

section Extend

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ[ε] R] [Algebra ℂ[ε] S]
  [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S] [IsScalarTower ℂ[ε] R S]

/-- The actual ring homomorphism on closed fibres associated to the map of thick charts. -/
def closedMap : Fibre (k := ℂ) R →ₐ[R] Fibre (k := ℂ) S :=
  Ideal.quotientMapₐ (epsilonIdeal (k := ℂ) S) (Algebra.ofId R S) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change algebraMap R S (algebraMap ℂ[ε] R ε) ∈ epsilonIdeal (k := ℂ) S
    rw [← IsScalarTower.algebraMap_apply]
    exact Ideal.subset_span (Set.mem_singleton _))

variable [Algebra.FormallyEtale R S]

/-- The extension of a time velocity through an affine open chart, using the
étale Kähler base-change isomorphism with coefficients in its closed fibre. -/
def extend (v : Derivation ℂ R (Fibre (k := ℂ) R)) : Derivation ℂ S (Fibre (k := ℂ) S) :=
  (KaehlerDifferential.linearMapEquivDerivation ℂ S)
    ((((closedMap R S).toLinearMap.comp v.liftKaehlerDifferential).liftBaseChange S).comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ R S).symm.toLinearMap)

theorem extend_on_chart (v : Derivation ℂ R (Fibre (k := ℂ) R)) (x : R) :
    extend R S v (algebraMap R S x) = closedMap R S (v x) := by
  change (((closedMap R S).toLinearMap.comp v.liftKaehlerDifferential).liftBaseChange S)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ R S).symm
      (KaehlerDifferential.D ℂ S (algebraMap R S x))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply, Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- Evaluation of a pulled-back chart form uses the original chart velocity with
its coefficients restricted to the smaller closed fibre. -/
theorem extend_contract_pull (v : Derivation ℂ R (Fibre (k := ℂ) R))
    (ω : ⋀[R]^2 (KaehlerDifferential ℂ R)) :
    contractRestrict (extend R S v) (CycleQ2CurveCylinderPullback.pullTwo R S ω) =
      contractRestrict ((closedMap R S).toLinearMap.compDer v) ω := by
  rw [CycleQ2CurveCylinderPullback.contract_pullTwo]
  have e : (extend R S v).compAlgebraMap R = (closedMap R S).toLinearMap.compDer v := by
    ext x
    exact extend_on_chart R S v x
  rw [e]

/-- Étale base change makes agreement on the original chart functions sufficient to
identify an independently restricted sheaf derivation with the chart velocity. -/
theorem extend_unique (v : Derivation ℂ R (Fibre (k := ℂ) R))
    (u : Derivation ℂ S (Fibre (k := ℂ) S))
    (hu : ∀ x : R, u (algebraMap R S x) = closedMap R S (v x)) : u = extend R S v := by
  let w := extend R S v
  let m := KaehlerDifferential.map ℂ ℂ R S
  have he : (u.liftKaehlerDifferential.restrictScalars R).comp m =
      (w.liftKaehlerDifferential.restrictScalars R).comp m := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    change u.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ R S (KaehlerDifferential.D ℂ R x)) =
      w.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ R S (KaehlerDifferential.D ℂ R x))
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D, hu, extend_on_chart]
  have hl := (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ R S).algHom_ext
    u.liftKaehlerDifferential w.liftKaehlerDifferential (LinearMap.congr_fun he)
  ext x
  exact (u.liftKaehlerDifferential_comp_D x).symm.trans
    ((LinearMap.congr_fun hl (KaehlerDifferential.D ℂ S x)).trans (w.liftKaehlerDifferential_comp_D x))

theorem extend_epsilon (v : Derivation ℂ R (Fibre (k := ℂ) R))
    (hv : v (algebraMap ℂ[ε] R ε) = 1) : extend R S v (algebraMap ℂ[ε] S ε) = 1 := by
  rw [IsScalarTower.algebraMap_apply ℂ[ε] R S, extend_on_chart, hv, map_one]

end Extend

open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2FirstOrderChartReduction CycleQ2FirstOrderCurve

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralCylinderEvaluation.familyRing
  CycleQ2LiteralCylinderEvaluation.closedRing
  CycleQ2CurveParameterTangent.chartComplexAlgebra
  CycleQ2LiteralCylinderEvaluation.familyComplexSMul
  CycleQ2LiteralCylinderEvaluation.familyComplexModule
  CycleQ2LiteralCylinderEvaluation.reductionAlgebra
  CycleQ2LiteralCylinderEvaluation.familyReductionTower

variable (t : Fin 3 → ℂ) (i : Fin 4)
variable (S : Type) [CommRing S] [Algebra ℂ[ε] S] [Algebra ℂ S] [IsScalarTower ℂ ℂ[ε] S]
variable (f : B t i →ₐ[ℂ[ε]] S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]

private def back : A t i ≃ₗ[B t i] Fibre (k := ℂ) (B t i) :=
  (LinearEquiv.ofBijective (specializeFibre t i) (curveChartReductionEquiv t i).bijective).symm

section ChartMap

omit [Algebra ℂ S] [IsScalarTower ℂ ℂ[ε] S] [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] in
private theorem chartDual : letI := f.toRingHom.toAlgebra; IsScalarTower ℂ[ε] (B t i) S := by
  let := f.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm

omit [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] in
private theorem chartComplex : letI := f.toRingHom.toAlgebra; IsScalarTower ℂ (B t i) S := by
  let := f.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (R := ℂ) (S := B t i) (A := S) (fun c => by
    change algebraMap ℂ S c = f (algebraMap ℂ (B t i) c)
    rw [chartMap_constant, f.commutes, ← IsScalarTower.algebraMap_apply ℂ ℂ[ε] S])

omit [Algebra ℂ S] [IsScalarTower ℂ ℂ[ε] S] in
private theorem chartEtale : letI := f.toRingHom.toAlgebra; Algebra.FormallyEtale (B t i) S := by
  let := f.toRingHom.toAlgebra
  have h : Algebra.Etale (B t i) S := (RingHom.etale_algebraMap).mp
    ((HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp
      (show AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom f.toRingHom)) from inferInstance))
  infer_instance

/-- Restriction of the actual epsilon-quotient rings. -/
def onClosed : Fibre (k := ℂ) (B t i) →+* Fibre (k := ℂ) S :=
  Ideal.quotientMap _ f.toRingHom (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change f (algebraMap ℂ[ε] (B t i) ε) ∈ epsilonIdeal (k := ℂ) S
    rw [f.commutes]
    exact Ideal.subset_span (Set.mem_singleton _))

/-- Restriction of a velocity on an actual moving curve chart, with its original seed coefficient ring. -/
def restrictVelocity (v : Derivation ℂ (B t i) (A t i)) : Derivation ℂ S (Fibre (k := ℂ) S) := by
  letI := f.toRingHom.toAlgebra
  letI := chartDual t i S f
  letI := chartComplex t i S f
  letI := chartEtale t i S f
  exact extend (B t i) S ((back t i).toLinearMap.compDer v)

theorem restrictVelocity_on_chart (v : Derivation ℂ (B t i) (A t i)) (x : B t i) :
    restrictVelocity t i S f v (f x) = onClosed t i S f (back t i (v x)) := by
  let := f.toRingHom.toAlgebra
  let := chartDual t i S f
  let := chartComplex t i S f
  let := chartEtale t i S f
  exact extend_on_chart (B t i) S ((back t i).toLinearMap.compDer v) x

theorem restrictVelocity_epsilon (v : Derivation ℂ (B t i) (A t i))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) :
    restrictVelocity t i S f v (algebraMap ℂ[ε] S ε) = 1 := by
  have hb : back t i 1 = 1 := by
    apply (back t i).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact (map_one (curveChartReductionEquiv t i)).symm
  rw [← f.commutes ε, restrictVelocity_on_chart, hv, hb, map_one]

end ChartMap

end CycleQ2LiteralAbelJacobiEvaluationOverlapVelocity
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationOverlapVelocity.restrictVelocity_epsilon
#print axioms CycleQ2LiteralAbelJacobiEvaluationOverlapVelocity.extend_contract_pull
