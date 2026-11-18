import Proposal.GeometricIncidenceIntegralComponent
import Proposal.GeometricIntegralCurveNormalizationSection
import Proposal.GeometricLiteralIncidenceGenericModel
import Proposal.GeometricNormalGenericChart
import Proposal.GeometricProperGenericSmoothNeighborhood
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# A proper time model smooth over a nonempty coefficient open

The absolute normalization of an integral component is finite. Its generic
fiber has normal affine domain charts. The finite map to the original curve
bounds their dimension, hence the entire generic fiber is smooth. Properness
then gives a smooth model above an open of the full monic coefficient space.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceProperSmoothModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2IncidenceEtaleParameter
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2GenericPointAffineSections
  CycleQ2NormalGenericChart

/-- The same boundary dimension bound applies to any proper model with a dense smooth time open. -/
private theorem generic_chart_dimension {X Y : Scheme} [NoetherianSpace X] (j : X ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] (p : Y ⟶ monicBase) [IsProper p]
    (hs : SmoothOfRelativeDimension 1 (j ≫ p)) {W : (pullback (genericMorphism MonicRing) p).Opens}
    (hW : IsAffineOpen W) : Ring.KrullDimLE 1 Γ(pullback (genericMorphism MonicRing) p, W) := by
  let F : Scheme := pullback (genericMorphism MonicRing) p
  let T : Scheme := pullback (pullback.snd (genericMorphism MonicRing) p) j
  let a : T ⟶ F := pullback.fst (pullback.snd (genericMorphism MonicRing) p) j
  let b : F ⟶ Spec (CommRingCat.of (FractionRing MonicRing)) := pullback.fst (genericMorphism MonicRing) p
  have : NoetherianSpace F := CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper b
  have : NoetherianSpace T :=
    a.isOpenEmbedding.isInducing.noetherianSpace
  have : Flat (genericMorphism MonicRing) := (inferInstance : Flat CycleQ2LiteralIncidenceGenericModel.genericMorphism)
  have : IsDominant a := CycleQ2DominantFlatBaseChange.pullback_fst_dominant _ _
  have : SmoothOfRelativeDimension 1 (a ≫ b) := CycleQ2LiteralIncidenceGenericModel.generic_open_smooth j p hs
  exact CycleQ2CurveChartDimension.chart_dimension a b hW

variable {X : Scheme} [IsIntegral X] (p : X ⟶ monicBase) [IsProper p] [IsDominant p]

private def coefficients (U : X.Opens) : CommRingCat.of MonicRing ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of MonicRing)).inv ≫ p.appLE ⊤ U (by simp)

private theorem affine_over {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ p = Spec.map (coefficients p U) := by
  rw [coefficients, Spec.map_comp]
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU (by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  exact h.symm

private theorem coefficients_injective {U : X.Opens} (hU : IsAffineOpen U)
    [Nontrivial Γ(X,U)] : Function.Injective (coefficients p U).hom := by
  have : IsDominant hU.fromSpec :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ hU.fromSpec.isOpenMap⟩
  have : IsDominant (Spec.map (coefficients p U)) := by rw [← affine_over p hU]; infer_instance
  have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (coefficients p U).hom).mp
    (Spec.map (coefficients p U)).denseRange
  exact (RingHom.injective_iff_ker_eq_bot _).mpr (le_bot_iff.mp (by simpa [nilradical_eq_zero] using h))

private instance : LocallyOfFiniteType toComplex := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ MonicRing)

/-- All points of the generic fiber of the finite normalization are smooth, including
the points over the boundary of the original smooth time open. -/
theorem normalization_generic_smooth
    (hd : ∀ W : (pullback (genericMorphism MonicRing) p).affineOpens,
      Ring.KrullDimLE 1 Γ(pullback (genericMorphism MonicRing) p, W.1)) :
    Smooth (pullback.fst (genericMorphism MonicRing) (CycleQ2IntegralCurveNormalization.normalize X ≫ p)) := by
  let j := point X
  apply smooth_generic_of_cover _ j.normalizationOpenCover
  intro U
  rw [← Category.assoc, Scheme.Hom.ι_fromNormalization, Category.assoc, affine_over p U.2, ← Spec.map_comp]
  let A := Γ(X,U.1)
  let L := Γ(pointScheme X, j ⁻¹ᵁ U.1)
  let : Algebra A L := (j.app U.1).hom.toAlgebra
  let N := integralClosure A L
  let : Algebra MonicRing A := (coefficients p U.1).hom.toAlgebra
  let : Algebra MonicRing N := ((algebraMap A N).comp (algebraMap MonicRing A)).toAlgebra
  let : IsScalarTower MonicRing A N := .of_algebraMap_eq' rfl
  change Smooth (pullback.fst (genericMorphism MonicRing) (Spec.map (CommRingCat.ofHom (algebraMap MonicRing N))))
  apply smooth_affine_of_generic_algebra
  rcases subsingleton_or_nontrivial A with hs | ht
  · let : Subsingleton N := Algebra.subsingleton A _
    let _ : Algebra N (GenericRing MonicRing N) := Algebra.TensorProduct.rightAlgebra
    let : Subsingleton (GenericRing MonicRing N) := Algebra.subsingleton N _
    infer_instance
  let : Nonempty U.1 := CycleQ2IntegralCurveNormalization.nonempty_chart U.2
  let : Field L := (native_isField X U.1).toField
  have hi : Function.Injective (algebraMap MonicRing A) := coefficients_injective p U.2
  have hAN : Function.Injective (algebraMap A N) := by
    let : IsFractionRing A L := native_isFractionRing X U.1 U.2
    exact Function.Injective.of_comp (f := algebraMap N L) (IsFractionRing.injective A L)
  have hiN : Function.Injective (algebraMap MonicRing N) := hAN.comp hi
  have : IsIntegrallyClosed N := IsIntegrallyClosed.of_isIntegrallyClosedIn N L
  let : Algebra.FiniteType MonicRing A :=
    (p.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of MonicRing)).symm.commRingCatIsoToRingEquiv.surjective)
  let : Module.Finite A N := CycleQ2IntegralCurveNormalization.finite_chart ℂ (p ≫ toComplex) U.2
  let : Algebra.FiniteType MonicRing N :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType MonicRing A) inferInstance
  let : Ring.KrullDimLE 1 (GenericRing MonicRing A) := generic_patch_dimension p U.2.fromSpec (affine_over p U.2) hd
  let : IsDomain (GenericRing MonicRing A) := generic_domain hi
  let : IsDomain (GenericRing MonicRing N) := generic_domain hiN
  let : Ring.DimensionLEOne (GenericRing MonicRing A) := ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  let f := Algebra.TensorProduct.map (AlgHom.id MonicRing (FractionRing MonicRing)) (IsScalarTower.toAlgHom MonicRing A N)
  let : Algebra (GenericRing MonicRing A) (GenericRing MonicRing N) := f.toRingHom.toAlgebra
  let : Module.Finite (GenericRing MonicRing A) (GenericRing MonicRing N) :=
    RingHom.Finite.tensorProductMap (f := AlgHom.id MonicRing (FractionRing MonicRing)) (RingEquiv.refl _).finite
      (g := IsScalarTower.toAlgHom MonicRing A N) (RingHom.finite_algebraMap.mpr inferInstance)
  let : Ring.DimensionLEOne (GenericRing MonicRing N) := Ring.DimensionLEOne.of_isIntegral _ _
  exact generic_smooth hiN

theorem normalization_smooth_neighborhood
    (hd : ∀ W : (pullback (genericMorphism MonicRing) p).affineOpens,
      Ring.KrullDimLE 1 Γ(pullback (genericMorphism MonicRing) p, W.1)) :
    ∃ V : monicBase.Opens, genericMorphism MonicRing (default : Spec (CommRingCat.of (FractionRing MonicRing))) ∈ V ∧
      Smooth ((CycleQ2IntegralCurveNormalization.normalize X ≫ p) ∣_ V) ∧
      IsProper ((CycleQ2IntegralCurveNormalization.normalize X ≫ p) ∣_ V) := by
  let n := CycleQ2IntegralCurveNormalization.normalize X
  have : IsFinite n := CycleQ2IntegralCurveNormalization.finite ℂ (p ≫ toComplex)
  have : IsNoetherian monicBase := inferInstanceAs (IsNoetherian (Spec (CommRingCat.of MonicRing)))
  have : LocallyOfFinitePresentation (n ≫ p) := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  obtain ⟨V, hv, hs⟩ := CycleQ2ProperGenericSmoothNeighborhood.exists_smooth_neighborhood (n ≫ p)
    (normalization_generic_smooth p hd)
  exact ⟨V, hv, hs, inferInstance⟩

/-- A dense open of the original time open lifts isomorphically to an open
of the finite normalization, with the actual map to the original component. -/
theorem normalization_recovers_open {T : Scheme} (a : T ⟶ X)
    [IsOpenImmersion a] [IsDominant a] :
    ∃ D : T.Opens, (D : Set T).Nonempty ∧
      ∃ j : D.toScheme ⟶ CycleQ2IntegralCurveNormalization.Model X,
        IsOpenImmersion j ∧ IsDominant j ∧
        j ≫ CycleQ2IntegralCurveNormalization.normalize X = D.ι ≫ a := by
  let n := CycleQ2IntegralCurveNormalization.normalize X
  obtain ⟨G, hg, hG⟩ := CycleQ2IntegralCurveNormalization.iso_over_generic_open ℂ (p ≫ toComplex)
  let D := a ⁻¹ᵁ G
  have hD : (D : Set T).Nonempty := a.denseRange.exists_mem_open G.isOpen ⟨_, hg⟩
  let j := (a ∣_ G) ≫ inv (n ∣_ G) ≫ (n ⁻¹ᵁ G).ι
  have : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have : Nonempty D.toScheme := hD.to_subtype
  have : IsDominant j := ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ j.isOpenMap⟩
  refine ⟨D, hD, j, inferInstance, inferInstance, ?_⟩
  simp only [j, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]

open CycleQ2LiteralIncidenceRelativeCompletion

/-- Every nonempty open test in the literal time family selects an integral proper
component. Its finite normalization is proper and smooth over a coefficient open
containing the generic sextic. -/
theorem test_proper_smooth_model (V : parameterScheme.Opens) (W : (Time toRaw V).Opens)
    (hW : (W : Set (Time toRaw V)).Nonempty) :
    ∃ U : (Time toRaw V).Opens, U ≤ W ∧ IsIntegral U.toScheme ∧
      ∃ hI : IsIntegral (CycleQ2IncidenceIntegralComponent.Model (inclusion V) U),
      let p := CycleQ2IncidenceIntegralComponent.toBase (inclusion V) (structureMap V) U
      let n := @CycleQ2IntegralCurveNormalization.normalize _ hI
      IsFinite n ∧ IsProper (n ≫ p) ∧ Surjective (n ≫ p) ∧
        ∃ E : U.toScheme.Opens, (E : Set U.toScheme).Nonempty ∧
          ∃ j : E.toScheme ⟶ _, IsOpenImmersion j ∧ IsDominant j ∧
            j ≫ n = E.ι ≫ CycleQ2IncidenceIntegralComponent.openInclusion (inclusion V) U ∧
            ∃ D : monicBase.Opens,
              genericMorphism MonicRing (default : Spec (CommRingCat.of (FractionRing MonicRing))) ∈ D ∧
              (D : Set monicBase) ⊆ Set.range (j ≫ n ≫ p) ∧
              Smooth ((n ≫ p) ∣_ D) ∧ IsProper ((n ≫ p) ∣_ D) := by
  obtain ⟨U, hU, hi, hI, hs, hd, hsur⟩ := CycleQ2IncidenceIntegralComponent.monic_exists_model V W hW
  let Y := CycleQ2IncidenceIntegralComponent.Model (inclusion V) U
  let p := CycleQ2IncidenceIntegralComponent.toBase (inclusion V) (structureMap V) U
  let a := CycleQ2IncidenceIntegralComponent.openInclusion (inclusion V) U
  let n := CycleQ2IntegralCurveNormalization.normalize Y
  have : IsFinite n := CycleQ2IntegralCurveNormalization.finite ℂ (p ≫ toComplex)
  have : IsDominant (point Y) := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq]
    rw [Scheme.range_fromSpecResidueField]
    exact genericPoint_spec Y
  have : IsDominant ((point Y).toNormalization ≫ n) := by
    change IsDominant ((point Y).toNormalization ≫ (point Y).fromNormalization)
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  have : IsDominant n := IsDominant.of_comp (point Y).toNormalization n
  have : Surjective n := surjective_of_isDominant_of_isClosed_range _ n.isClosedMap.isClosed_range
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set (Time toRaw V))
  obtain ⟨E, hE, j, hj, hjd, hjn⟩ := normalization_recovers_open p a
  obtain ⟨B, hB, hsB, _⟩ := normalization_smooth_neighborhood p
    (fun D => generic_chart_dimension a p hs D.2)
  let f := j ≫ n ≫ p
  have : SmoothOfRelativeDimension 1 f := by
    rw [show f = E.ι ≫ a ≫ p by simp only [f, ← Category.assoc, hjn]]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 E.ι (a ≫ p)
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 _
  have : Nonempty E.toScheme := hE.to_subtype
  let G : monicBase.Opens := ⟨Set.range f, f.isOpenMap.isOpen_range⟩
  have hg : genericMorphism MonicRing (default : Spec (CommRingCat.of (FractionRing MonicRing))) ∈ G :=
    ((CycleQ2LiteralIncidenceGenericModel.generic_value default).mem_open_set_iff G.isOpen).mpr
      (by simpa only [Set.univ_inter] using Set.range_nonempty f)
  let D := B ⊓ G
  have hD : D ≤ B := inf_le_left
  have hsm : Smooth ((n ≫ p) ∣_ D) := by
    apply MorphismProperty.of_postcomp (W' := @IsOpenImmersion) @Smooth _ (monicBase.homOfLE hD) inferInstance
    rw [morphismRestrict_homOfLE]
    infer_instance
  exact ⟨U, hU, hi, hI, inferInstance, inferInstance, inferInstance, E, hE, j, hj, hjd, hjn,
    D, ⟨hB, hg⟩, fun _ hx => hx.2, hsm, inferInstance⟩

end CycleQ2LiteralIncidenceProperSmoothModel
end

#print axioms CycleQ2LiteralIncidenceProperSmoothModel.normalization_generic_smooth
#print axioms CycleQ2LiteralIncidenceProperSmoothModel.normalization_smooth_neighborhood

#print axioms CycleQ2LiteralIncidenceProperSmoothModel.test_proper_smooth_model
