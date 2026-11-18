import Proposal.GeometricLiteralIncidenceRelativeNormalization
import Proposal.GeometricDominantFlatBaseChange
import Proposal.GeometricCurveChartDimension

/-!
# The proper generic parameter curve over the monic sextic function field

On the generic coefficient fiber the original smooth time open is dense in
the finite model. Every affine chart of the proper fiber has Krull dimension
at most one. The generic fiber is nonempty for the marked time neighborhood.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceGenericModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeNormalization

abbrev K := FractionRing MonicRing

def genericMorphism : Spec (CommRingCat.of K) ⟶ monicBase :=
  Spec.map (CommRingCat.ofHom (algebraMap MonicRing K))

instance : Flat genericMorphism := by
  apply (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem generic_value (s : Spec (CommRingCat.of K)) :
    IsGenericPoint (genericMorphism s) Set.univ := by
  have hd : DenseRange genericMorphism := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap MonicRing K)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective MonicRing K)]
    exact bot_le
  have hr : Set.range genericMorphism = {genericMorphism s} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg genericMorphism (Subsingleton.elim z s)
    · rintro rfl
      exact ⟨s, rfl⟩
  change closure {genericMorphism s} = Set.univ
  rw [← hr]
  exact hd.closure_range

variable (V : parameterScheme.Opens)

abbrev Fiber := pullback genericMorphism (normalizedMap V)

abbrev projection : Fiber V ⟶ Spec (CommRingCat.of K) := pullback.fst _ _

abbrev TimeFiber := pullback (pullback.snd genericMorphism (normalizedMap V)) (openInclusion V)

abbrev inclusion : TimeFiber V ⟶ Fiber V := pullback.fst _ _

theorem noetherian_of_proper {X Y : Scheme} [IsNoetherian Y] (p : X ⟶ Y)
    [IsProper p] : NoetherianSpace X := by
  have := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := ⟨⟩
  infer_instance

instance : IsDominant (inclusion V) := by
  have : IsNoetherian monicBase := inferInstanceAs (IsNoetherian (Spec (CommRingCat.of MonicRing)))
  have : NoetherianSpace (Model V) := noetherian_of_proper (normalizedMap V)
  have : NoetherianSpace (Time toRaw V) :=
    (openInclusion V).isOpenEmbedding.isInducing.noetherianSpace
  exact CycleQ2DominantFlatBaseChange.pullback_fst_dominant _ _

theorem generic_open_smooth {X Y : Scheme} (j : X ⟶ Y) (p : Y ⟶ monicBase)
    (hs : SmoothOfRelativeDimension 1 (j ≫ p)) :
    SmoothOfRelativeDimension 1
      (pullback.fst (pullback.snd genericMorphism p) j ≫ pullback.fst genericMorphism p) := by
  let e := pullbackLeftPullbackSndIso genericMorphism p j
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    e.inv _).mp
  rw [show e.inv ≫ pullback.fst (pullback.snd genericMorphism p) j ≫ pullback.fst genericMorphism p =
    pullback.fst genericMorphism (j ≫ p) from pullbackLeftPullbackSndIso_inv_fst ..]
  let _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_fst _ _ hs

instance : SmoothOfRelativeDimension 1 (inclusion V ≫ projection V) :=
  generic_open_smooth _ _ (normalized_time_model V).2.2.2

instance : AlgebraicGeometry.IsReduced (TimeFiber V) :=
  reduced_of_smooth_over_domain 1 (inclusion V ≫ projection V)

/-- Any nonempty marked test open survives on the generic coefficient fiber. -/
theorem test_meets_generic (W : (Time toRaw V).Opens) (hW : (W : Set (Time toRaw V)).Nonempty) :
    ∃ x : TimeFiber V, pullback.snd (pullback.snd genericMorphism (normalizedMap V)) (openInclusion V) x ∈ W := by
  have := timeMap_smooth toRaw V
  have : Smooth (timeMap toRaw V) := SmoothOfRelativeDimension.smooth 1 _
  have hg := ((generic_value default).mem_open_set_iff ((timeMap toRaw V).isOpenMap _ W.isOpen)).mpr
    (by simpa only [Set.univ_inter] using hW.image (timeMap toRaw V))
  obtain ⟨y, hy, he⟩ := hg
  have h : genericMorphism default = (openInclusion V ≫ normalizedMap V) y := by
    rw [open_over]
    exact he.symm
  obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := genericMorphism) (g := openInclusion V ≫ normalizedMap V) default y h
  refine ⟨(pullbackLeftPullbackSndIso genericMorphism (normalizedMap V) (openInclusion V)).inv z, ?_⟩
  rwa [← Scheme.Hom.comp_apply, pullbackLeftPullbackSndIso_inv_snd_snd, hz]

/-- The dimension bound holds on every affine chart, including those meeting the boundary. -/
theorem chart_dimension {W : (Fiber V).Opens} (hW : IsAffineOpen W) :
    Ring.KrullDimLE 1 Γ(Fiber V, W) := by
  have : NoetherianSpace (Fiber V) := noetherian_of_proper (projection V)
  have : NoetherianSpace (TimeFiber V) := (inclusion V).isOpenEmbedding.isInducing.noetherianSpace
  exact CycleQ2CurveChartDimension.chart_dimension (inclusion V) (projection V) hW

/-- A marked neighborhood has a nonempty proper generic fiber and its smooth open is dense. -/
theorem exists_proper_generic_curve (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧ Surjective (projection V) ∧
      IsProper (projection V) ∧ IsDominant (inclusion V) ∧
      SmoothOfRelativeDimension 1 (inclusion V ≫ projection V) ∧
      ∀ W : (Fiber V).affineOpens, Ring.KrullDimLE 1 Γ(Fiber V, W.1) := by
  obtain ⟨W, hW, _, _, _, _, _, hsur⟩ := exists_surjective_completion t hi
  have : IsDominant (openInclusion W ≫ toCompletion W) := by rw [open_toCompletion]; infer_instance
  have := IsDominant.of_comp (openInclusion W) (toCompletion W)
  have : Surjective (toCompletion W) :=
    surjective_of_isDominant_of_isClosed_range _ (toCompletion W).isClosedMap.isClosed_range
  have : Surjective (normalizedMap W) := by unfold normalizedMap; infer_instance
  exact ⟨W, hW, inferInstance, inferInstance, inferInstance, inferInstance, fun U =>
    chart_dimension W U.2⟩

end CycleQ2LiteralIncidenceGenericModel
end

#print axioms CycleQ2LiteralIncidenceGenericModel.test_meets_generic
#print axioms CycleQ2LiteralIncidenceGenericModel.exists_proper_generic_curve
