import Proposal.GeometricLiteralAbelJacobiEvaluationOverlap
import Proposal.GeometricLiteralAbelJacobiEvaluationOverlapVelocity
import Proposal.GeometricLiteralAbelJacobiTimeContraction
import Proposal.GeometricLiteralAbelJacobiSmoothNormalDimension
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Evaluation on common affine restrictions of two original moving curve charts

The closed fibre of an affine open of the moving germ is smooth of
relative dimension one. Velocities from any two original charts
therefore give equal contractions after restriction to a common open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationOverlap
open scoped DualNumber TensorProduct
open CategoryTheory AlgebraicGeometry
open CycleQ2FirstOrderCurve CycleQ2CurveParameterTangent CycleQ2DualNumberRegularQuotient
  CycleQ2LiteralAbelJacobiContraction CycleQ2CurveNormalContraction
  CycleQ2LiteralAbelJacobiTimeContraction CycleQ2FirstOrderTensorReduction

private theorem quotient_dimension {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R S)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  have hi := RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))
  have ht := (RingHom.locally_isStableUnderBaseChange
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))
    (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange 1)).tensorProduct (R ⧸ I) h
  have he := hi.1 (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] S)) e.symm.toRingEquiv ht
  convert he using 1
  exact RingHom.ext fun c => (e.symm.commutes c).symm

private theorem quotient_dimension_at_residue {k R S : Type} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S] (I : Ideal R)
    (e : (R ⧸ I) ≃+* k) (he : ∀ x : k, e.symm x = Ideal.Quotient.mk I (algebraMap k R x))
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R S)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k (S ⧸ I.map (algebraMap R S))) := by
  let f := algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))
  have hq := quotient_dimension I h
  have hc := (RingHom.locally_respectsIso
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))).2 f e.symm hq
  have hf : algebraMap k (S ⧸ I.map (algebraMap R S)) = f.comp e.symm.toRingHom := by
    apply RingHom.ext
    intro x
    change Ideal.Quotient.mk _ (algebraMap k S x) = f (e.symm x)
    rw [he]
    exact congrArg (Ideal.Quotient.mk _) (IsScalarTower.algebraMap_apply k R S x)
  rw [hf]
  exact hc

private abbrev E := (Ideal.span {ε} : Ideal ℂ[ε])

private abbrev residue : ℂ[ε] →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

private def residueEquiv : (ℂ[ε] ⧸ E) ≃+* ℂ :=
  (Ideal.quotEquivOfEq (show E = RingHom.ker residue from firstOrderFst_ker.symm)).trans
    (RingHom.quotientKerEquivOfSurjective (f := residue) firstOrderFst_surjective)

private theorem residueEquiv_mk (p : ℂ[ε]) : residueEquiv (Ideal.Quotient.mk E p) = p.fst := rfl

section ClosedFibre

variable (S : Type) [CommRing S] [Algebra ℂ[ε] S] [Algebra ℂ S] [IsScalarTower ℂ ℂ[ε] S]

omit [Algebra ℂ S] [IsScalarTower ℂ ℂ[ε] S] in
private theorem eps_map : E.map (algebraMap ℂ[ε] S) = epsilonIdeal (k := ℂ) S := by
  rw [E, Ideal.map_span, Set.image_singleton]
  rfl

/-- Base change of a dual-number affine smooth curve to the original complex point. -/
theorem closed_locally_smooth
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap ℂ[ε] S)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℂ (Fibre (k := ℂ) S)) := by
  have he (x : ℂ) : residueEquiv.symm x = Ideal.Quotient.mk E (algebraMap ℂ ℂ[ε] x) :=
    residueEquiv.injective (by rw [RingEquiv.apply_symm_apply, residueEquiv_mk]; rfl)
  have hs := quotient_dimension_at_residue (S := S) E residueEquiv he h
  change RingHom.Locally _ (algebraMap ℂ (S ⧸ epsilonIdeal (k := ℂ) S))
  rw [← eps_map S]
  exact hs

end ClosedFibre

open CycleQ2LiteralAbelJacobiSmoothNormalDimension CycleQ2LiteralAbelJacobiSeedLiftDimension

/-- The original algebraically independent coefficients give a one-dimensional infinitesimal germ. -/
theorem germ_dimension (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) :
    SmoothOfRelativeDimension 1 (firstOrderCurveToBase t) := by
  obtain ⟨V, hV, hdim, _, _⟩ := dimension_one_neighborhood_of_seedMinorCover t
    (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht)
  exact firstOrderCurve_dimension_of_neighborhood t V hV hdim

section Affine

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t)
variable (S : Type) [CommRing S] [Algebra ℂ[ε] S] [Algebra ℂ S] [IsScalarTower ℂ ℂ[ε] S]
variable (j : Spec (CommRingCat.of S) ⟶ firstOrderCurve t) [IsOpenImmersion j]
variable (hj : j ≫ firstOrderCurveToBase t = Spec.map (CommRingCat.ofHom (algebraMap ℂ[ε] S)))

include ht hj in
theorem affine_closed_dimension : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
    (algebraMap ℂ (Fibre (k := ℂ) S)) := by
  have := germ_dimension t ht
  have hs : SmoothOfRelativeDimension 1 (j ≫ firstOrderCurveToBase t) := smoothOfRelativeDimension_comp 0 1 _ _
  rw [hj] at hs
  exact closed_locally_smooth S ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp hs)

include ht hj in
/-- Evaluation of the family's two-forms is independent of the chosen time lift on
any affine subopen of the original moving germ, in particular on affine overlap refinements. -/
theorem affine_evaluation_unique
    (v w : Derivation ℂ S (Fibre (k := ℂ) S))
    (hv : v (algebraMap ℂ[ε] S ε) = 1) (hw : w (algebraMap ℂ[ε] S ε) = 1) :
    contractRestrict v = contractRestrict w := by
  have := exteriorTwo_subsingleton_of_curve (affine_closed_dimension t ht S j hj)
  have hk : RingHom.ker (algebraMap S (Fibre (k := ℂ) S)) = epsilonIdeal (k := ℂ) S := Ideal.mk_ker
  exact contract_eq_of_epsilon (S := S) (C := Fibre (k := ℂ) S) (algebraMap ℂ[ε] S ε)
    (show Function.Surjective (algebraMap S (Fibre (k := ℂ) S)) from Ideal.Quotient.mk_surjective) hk v w hv hw

include ht hj in
/-- The same equality in a complex coordinate presentation of the actual closed fibre. -/
theorem affine_evaluation_transport (C : Type) [CommRing C] [Algebra ℂ C]
    [Algebra S C] [IsScalarTower ℂ S C] (e : Fibre (k := ℂ) S ≃ₐ[ℂ] C)
    (he : ∀ s : S, e (Ideal.Quotient.mk _ s) = algebraMap S C s)
    (v w : Derivation ℂ S C) (hv : v (algebraMap ℂ[ε] S ε) = 1)
    (hw : w (algebraMap ℂ[ε] S ε) = 1) : contractRestrict v = contractRestrict w := by
  have hc := (RingHom.locally_respectsIso
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))).1
    (algebraMap ℂ (Fibre (k := ℂ) S)) e.toRingEquiv (affine_closed_dimension t ht S j hj)
  have hc' : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap ℂ C) := by
    convert hc using 1
    exact RingHom.ext fun c => (e.commutes c).symm
  have := exteriorTwo_subsingleton_of_curve hc'
  have surj : Function.Surjective (algebraMap S C) := by
    intro c
    obtain ⟨a, rfl⟩ := e.surjective c
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨s, (he s).symm⟩
  have hk : RingHom.ker (algebraMap S C) = epsilonIdeal (k := ℂ) S := by
    ext x
    constructor
    · intro hx
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply e.injective
      exact ((he x).trans hx).trans (map_zero e).symm
    · intro hx
      change algebraMap S C x = 0
      rw [← he, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  exact contract_eq_of_epsilon (algebraMap ℂ[ε] S ε) surj hk v w hv hw

end Affine
end CycleQ2LiteralAbelJacobiEvaluationOverlap

namespace CycleQ2LiteralAbelJacobiEvaluationOverlapCharts
open CategoryTheory AlgebraicGeometry
open scoped DualNumber
open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiEvaluationOverlap CycleQ2LiteralAbelJacobiEvaluationOverlapVelocity
  CycleQ2FirstOrderCurve

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
variable (f : B t i →ₐ[ℂ[ε]] S)
variable (hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)))

/-- The restricted velocity with the open immersion supplied explicitly. -/
abbrev chartVelocity (v : Derivation ℂ (B t i) (A t i)) :
    Derivation ℂ S (CycleQ2CurveParameterTangent.Fibre (k := ℂ) S) := by
  letI := hf
  exact restrictVelocity t i S f v

private theorem chartVelocity_one (v : Derivation ℂ (B t i) (A t i))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) :
    chartVelocity t i S f hf v (algebraMap ℂ[ε] S ε) = 1 := by
  let := hf
  exact restrictVelocity_epsilon t i S f v hv

/-- The two chart evaluations agree on every two-form over any affine test open in their intersection. -/
theorem pair_evaluation (ht : AlgebraicIndependent ℚ t) (j : Fin 4)
    (g : B t j →ₐ[ℂ[ε]] S) (hg : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)))
    (v : Derivation ℂ (B t i) (A t i)) (w : Derivation ℂ (B t j) (A t j))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) (hw : w (algebraMap ℂ[ε] (B t j) ε) = 1) :
    contractRestrict (chartVelocity t i S f hf v) = contractRestrict (chartVelocity t j S g hg w) := by
  let := hf
  let u := Spec.map (CommRingCat.ofHom f.toRingHom) ≫ CycleQ2FirstOrderCurveCharts.firstOrderChartToCurve t i
  have hu : u ≫ firstOrderCurveToBase t = Spec.map (CommRingCat.ofHom (algebraMap ℂ[ε] S)) := by
    dsimp only [u]
    rw [Category.assoc, CycleQ2FirstOrderCurveCharts.firstOrderChartToCurve_overBase, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext f.commutes
  have : IsOpenImmersion u := by dsimp only [u]; infer_instance
  exact affine_evaluation_unique t ht S u hu _ _ (chartVelocity_one t i S f hf v hv)
    (chartVelocity_one t j S g hg w hw)

private theorem chart_velocity (ht : AlgebraicIndependent ℚ t) :
    ∃ v : Derivation ℂ (B t i) (A t i), v (algebraMap ℂ[ε] (B t i) ε) = 1 := by
  have h := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  have hs := CycleQ2LiteralAbelJacobiSeedLiftDimension.smooth_seed_of_seedMinorCover t h
  have := CycleQ2LiteralAbelJacobiSeedLiftRegular.firstOrderCurveChart_flat_of_smooth_seed t hs i
  have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t h i
  obtain ⟨v, hv, _⟩ := CycleQ2LiteralCylinderEvaluation.exists_evaluation t i
  exact ⟨v, hv⟩

/-- The actual flat curve on the same independent coefficients admits normalized velocities
on every chart simultaneously, with agreement of the contractions on any common affine open. -/
theorem exists_pair_evaluation (ht : AlgebraicIndependent ℚ t) (j : Fin 4)
    (g : B t j →ₐ[ℂ[ε]] S) (hg : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom))) :
    ∃ v : (a : Fin 4) → Derivation ℂ (B t a) (A t a),
      (∀ a : Fin 4, v a (algebraMap ℂ[ε] (B t a) ε) = 1) ∧
        contractRestrict (chartVelocity t i S f hf (v i)) =
          contractRestrict (chartVelocity t j S g hg (v j)) := by
  choose v hv using fun a => chart_velocity t a ht
  exact ⟨v, hv, pair_evaluation t i S f hf ht j g hg (v i) (v j) (hv i) (hv j)⟩

end CycleQ2LiteralAbelJacobiEvaluationOverlapCharts
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationOverlapCharts.pair_evaluation

#print axioms CycleQ2LiteralAbelJacobiEvaluationOverlapCharts.exists_pair_evaluation
