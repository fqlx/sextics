import Proposal.GeometricLiteralIncidenceRelativeCompletion
import Proposal.GeometricFiniteTypeNormalization
import Proposal.GeometricReducedNormalizationFinite
import Proposal.GeometricDenseOpenTotalFractions
import Proposal.GeometricDenseOpenAffineSections
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite relative normalization of the monic time compactification

Normalize the projective graph closure in its original smooth time open.
This map is finite and its inverse image of the whole time open is unchanged.
The resulting model stays proper over the original normalized coefficient base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceRelativeNormalization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceRelativeCompletion
open scoped TensorProduct

private theorem reduced_etale_over_domain {P A : Type} [CommRing P] [IsDomain P] [CommRing A]
    [Algebra P A] [Algebra.Etale P A] : _root_.IsReduced A := by
  let K := FractionRing P
  let : _root_.IsReduced (K ⊗[P] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[P] K ⊗[P] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective P K))

private theorem reduced_chart {R A : Type} [CommRing R] [IsDomain R] [CommRing A]
    (n : ℕ) (f : R →+* A) (hf : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f) :
    _root_.IsReduced A := by
  obtain ⟨s, hs, h⟩ := hf
  let (a : s) : _root_.IsReduced (Localization.Away a.val) := by
    obtain ⟨g, _, hg⟩ := (h _ a.property).exists_etale_mvPolynomial
    let := g.toAlgebra
    let : Algebra.Etale (MvPolynomial (Fin n) R) (Localization.Away a.val) := hg.toAlgebra
    exact reduced_etale_over_domain (P := MvPolynomial (Fin n) R)
  exact isReduced_of_injective _ (Localization.algebraMap_injective_of_span_eq_top s hs)

/-- A smooth scheme of fixed relative dimension over an affine integral base is reduced. -/
theorem reduced_of_smooth_over_domain {R : Type} [CommRing R] [IsDomain R] {X : Scheme}
    (n : ℕ) (f : X ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n f] :
    AlgebraicGeometry.IsReduced X := by
  apply (IsReduced.iff_of_openCover (X := X) X.affineCover).mpr
  intro a
  let Y := X.affineCover.X a
  let p := X.affineCover.f a ≫ f
  let c := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop
  have hp : SmoothOfRelativeDimension n p := by
    simpa only [Nat.zero_add, p] using smoothOfRelativeDimension_comp 0 n (X.affineCover.f a) f
  have he : Y.toSpecΓ ≫ Spec.map c = p := by
    dsimp only [c]
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have h : SmoothOfRelativeDimension n (Spec.map c) := by
    apply (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension n)
      Y.toSpecΓ (Spec.map c)).mp
    rwa [he]
  let : _root_.IsReduced Γ(Y, ⊤) := reduced_chart n c.hom
    ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mp h)
  exact isReduced_of_isAffine_isReduced (X := Y)

instance time_reduced (V : parameterScheme.Opens) : AlgebraicGeometry.IsReduced (Time toRaw V) := by
  have := timeMap_smooth toRaw V
  exact reduced_of_smooth_over_domain 1 (timeMap toRaw V)

instance completion_reduced (V : parameterScheme.Opens) : IsReduced (Completion V) := by
  let f := graph V
  apply (IsReduced.iff_of_openCover (X := f.image) f.ker.subschemeCover.openCover).mpr
  change ∀ W : ProjectiveBundle.affineOpens, IsReduced (Spec (CommRingCat.of (Γ(ProjectiveBundle, W.1) ⧸ f.ker.ideal W)))
  intro W
  apply (affine_isReduced_iff _).mpr
  let : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ W.1) :=
    isReduced_of_injective (f.toImage.app _).hom (f.toImage_app_injective W)
  exact isReduced_of_injective (f.ker.subschemeObjIso W).inv.hom
    (f.ker.subschemeObjIso W).symm.commRingCatIsoToRingEquiv.injective

/-- For a reduced scheme locally of finite type over the complex numbers, normalization
in any quasi-compact dense open is finite. -/
theorem dense_open_normalization_finite {X Y : Scheme} (j : X ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [IsDominant j] [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p] : IsFinite j.fromNormalization := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro V hV
  let A := Γ(Y, V)
  let B := Γ(X, j ⁻¹ᵁ V)
  let hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  let c := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ p.appLE ⊤ V hle
  let : Algebra ℂ A := c.hom.toAlgebra
  let : Algebra.FiniteType ℂ A :=
    (p.finiteType_appLE (isAffineOpen_top _) hV hle).comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  let : Algebra A B := (j.app V).hom.toAlgebra
  obtain ⟨φ, hφ⟩ := CycleQ2DenseOpenTotalFractions.sections_embedding A
    (CycleQ2DenseOpenAffineSections.chartOpen j hV) (CycleQ2DenseOpenAffineSections.dense j hV)
  let e := CycleQ2DenseOpenAffineSections.sectionEquiv j hV
  let : Module.Finite A (integralClosure A B) :=
    CycleQ2ReducedNormalizationFinite.finiteType_integralClosure_of_fraction_embedding ℂ
      CycleQ2FiniteTypeNormalization.domainNormalizationFinite A (φ.comp e.toAlgHom)
        (hφ.comp e.injective)
  rw [j.fromNormalization_app hV, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (j.normalizationObjIso hV).symm.commRingCatIsoToRingEquiv.surjective).comp
      (RingHom.finite_algebraMap.mpr inferInstance)

variable (V : parameterScheme.Opens)

abbrev Model := (inclusion V).normalization

def toCompletion : Model V ⟶ Completion V := (inclusion V).fromNormalization

def openInclusion : Time toRaw V ⟶ Model V := (inclusion V).toNormalization

def normalizedMap : Model V ⟶ monicBase := toCompletion V ≫ structureMap V

instance : IsOpenImmersion (openInclusion V) := inferInstanceAs (IsOpenImmersion (inclusion V).toNormalization)

instance : IsDominant (openInclusion V) := inferInstanceAs (IsDominant (inclusion V).toNormalization)

instance : IsFinite (toCompletion V) := by
  have : LocallyOfFiniteType toComplex := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ MonicRing)
  exact dense_open_normalization_finite (inclusion V) (structureMap V ≫ toComplex)

instance : IsProper (normalizedMap V) := by unfold normalizedMap; infer_instance

@[reassoc (attr := simp)] theorem open_toCompletion :
    openInclusion V ≫ toCompletion V = inclusion V := (inclusion V).toNormalization_fromNormalization

@[reassoc (attr := simp)] theorem open_over :
    openInclusion V ≫ normalizedMap V = timeMap toRaw V := by
  rw [normalizedMap, open_toCompletion_assoc, inclusion_over]

/-- The finite proper model contains exactly the original scheme over its marked time open. -/
theorem recovers_time_open : IsIso (pullback.snd (toCompletion V) (inclusion V)) := by
  let f := inclusion V
  change IsIso (pullback.snd f.fromNormalization f)
  rw [← isIso_comp_left_iff (f.normalizationPullback f), f.normalizationPullback_snd,
    ← isIso_comp_left_iff (pullback.snd f f).toNormalization,
    Scheme.Hom.toNormalization_fromNormalization]
  infer_instance

theorem normalized_time_model :
    IsProper (normalizedMap V) ∧ IsFinite (toCompletion V) ∧
      IsIso (pullback.snd (toCompletion V) (inclusion V)) ∧
      SmoothOfRelativeDimension 1 (openInclusion V ≫ normalizedMap V) := by
  refine ⟨inferInstance, inferInstance, recovers_time_open V, ?_⟩
  rw [open_over]
  exact timeMap_smooth _ _

end CycleQ2LiteralIncidenceRelativeNormalization
end

#print axioms CycleQ2LiteralIncidenceRelativeNormalization.normalized_time_model
