import Proposal.GeometricLiteralIncidenceRelativeNormalization

/-!
# Integral proper components meeting a prescribed time open

A nonempty open of a Noetherian space contains a nonempty irreducible open.
Taking its schematic image in a proper compactification gives an integral
proper model. Its smooth time open maps openly to the irreducible base, so
the model surjects onto that base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IncidenceIntegralComponent

open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Every nonempty open in a Noetherian space contains an irreducible open. -/
theorem exists_irreducible_open {T : Type*} [TopologicalSpace T] [NoetherianSpace T]
    (W : Opens T) (hW : (W : Set T).Nonempty) :
    ∃ U : Opens T, U ≤ W ∧ IsIrreducible (U : Set T) := by
  obtain ⟨w, hw⟩ := hW
  have : NoetherianSpace W := NoetherianSpace.set (W : Set T)
  let Z := irreducibleComponent (⟨w, hw⟩ : W)
  have hZ : Z ∈ irreducibleComponents W := irreducibleComponent_mem_irreducibleComponents _
  obtain ⟨Q, hQ, hn, hQZ⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  have hcut : Z ∩ Q = Q := Set.inter_eq_right.mpr hQZ
  have hd : Z ⊆ closure Q := by
    rw [← hcut]
    exact subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 hQ (hcut.symm ▸ hn)
  have hc : closure Q = Z := (closure_minimal hQZ (isClosed_of_mem_irreducibleComponents _ hZ)).antisymm hd
  have hirr : IsIrreducible Q := isIrreducible_iff_closure.mp (hc.symm ▸ hZ.1)
  exact ⟨⟨Subtype.val '' Q, W.isOpen.isOpenMap_subtype_val _ hQ⟩,
    fun _ ⟨y, _, hy⟩ ↦ hy ▸ y.property, hirr.image _ continuous_subtype_val.continuousOn⟩

universe u
variable {X Y B : Scheme.{u}}

/-- The schematic image of a quasi-compact morphism from an integral scheme is integral. -/
theorem integral_image (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] : IsIntegral f.image := by
  have hr : IsIrreducible (Set.range f.toImage) := by
    simpa using (IrreducibleSpace.isIrreducible_univ X).image f.toImage f.toImage.continuous.continuousOn
  have hirr : IrreducibleSpace f.image := by
    apply (irreducibleSpace_def _).mpr
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hr.closure
  apply (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨hirr, ?_⟩
  apply (IsReduced.iff_of_openCover (X := f.image) f.ker.subschemeCover.openCover).mpr
  change ∀ V : Y.affineOpens, IsReduced (Spec (CommRingCat.of (Γ(Y, V.1) ⧸ f.ker.ideal V)))
  intro V
  apply (affine_isReduced_iff _).mpr
  let : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ V.1) :=
    isReduced_of_injective (f.toImage.app _).hom (f.toImage_app_injective V)
  exact isReduced_of_injective (f.ker.subschemeObjIso V).inv.hom
    (f.ker.subschemeObjIso V).symm.commRingCatIsoToRingEquiv.injective

variable [NoetherianSpace X] (j : X ⟶ Y) [IsOpenImmersion j]

private instance compact_open_map (U : X.Opens) : QuasiCompact (U.ι ≫ j) := by
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  infer_instance

/-- The schematic closure in the given compactification of the chosen test open. -/
abbrev Model (U : X.Opens) := (U.ι ≫ j).image

def openInclusion (U : X.Opens) : U.toScheme ⟶ Model j U := (U.ι ≫ j).toImage

instance (U : X.Opens) : IsOpenImmersion (openInclusion j U) :=
  inferInstanceAs (IsOpenImmersion (U.ι ≫ j).toImage)

instance (U : X.Opens) : IsDominant (openInclusion j U) :=
  inferInstanceAs (IsDominant (U.ι ≫ j).toImage)

instance (U : X.Opens) : QuasiCompact (openInclusion j U) := by
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  infer_instance

def toBase (p : Y ⟶ B) (U : X.Opens) : Model j U ⟶ B := (U.ι ≫ j).imageι ≫ p

omit [NoetherianSpace X] [IsOpenImmersion j] in
@[reassoc (attr := simp)] theorem openInclusion_over (p : Y ⟶ B) (U : X.Opens) :
    openInclusion j U ≫ toBase j p U = U.ι ≫ j ≫ p := by
  simp [openInclusion, toBase, ← Category.assoc]

instance proper (p : Y ⟶ B) [IsProper p] (U : X.Opens) : IsProper (toBase j p U) := by
  unfold toBase
  infer_instance

/-- A prescribed nonempty open contains the dense open of an integral proper model
dominating the coefficient space. -/
theorem exists_model [IsReduced X] [IrreducibleSpace B] (p : Y ⟶ B) [IsProper p]
    [SmoothOfRelativeDimension 1 (j ≫ p)] (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ U : X.Opens, U ≤ W ∧ IsIntegral U.toScheme ∧ IsIntegral (Model j U) ∧
      SmoothOfRelativeDimension 1 (openInclusion j U ≫ toBase j p U) ∧
      IsDominant (toBase j p U) ∧ Surjective (toBase j p U) := by
  obtain ⟨D, hle, hD⟩ := exists_irreducible_open W hW
  let U : X.Opens := D
  have hU : IsIrreducible (U : Set X) := hD
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hU
  have hint : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hs : SmoothOfRelativeDimension 1 (U.ι ≫ j ≫ p) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 U.ι (j ≫ p)
  have : Smooth (U.ι ≫ j ≫ p) := SmoothOfRelativeDimension.smooth 1 _
  have hd : IsDominant (openInclusion j U ≫ toBase j p U) := by
    rw [openInclusion_over]
    exact ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ (U.ι ≫ j ≫ p).isOpenMap⟩
  have hbase := IsDominant.of_comp (openInclusion j U) (toBase j p U)
  refine ⟨U, hle, hint, integral_image (U.ι ≫ j), ?_, hbase, ?_⟩
  · rwa [openInclusion_over]
  · exact surjective_of_isDominant_of_isClosed_range _ (toBase j p U).isClosedMap.isClosed_range

open CategoryTheory.Limits CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

/-- The monic time family has Noetherian underlying space. -/
instance time_noetherian (V : parameterScheme.Opens) : NoetherianSpace (Time toRaw V) := by
  let _ := Algebra.FiniteType.isNoetherianRing SexticRing ParameterAlgebra
  have : NoetherianSpace parameterScheme :=
    inferInstanceAs (NoetherianSpace (Spec (CommRingCat.of ParameterAlgebra)))
  have : NoetherianSpace V.toScheme := NoetherianSpace.set (V : Set parameterScheme)
  exact (pullback.snd toRaw (V.ι ≫ parameterToSextics)).isClosedEmbedding.isInducing.noetherianSpace

theorem monic_exists_model (V : parameterScheme.Opens)
    (W : (Time toRaw V).Opens) (hW : (W : Set (Time toRaw V)).Nonempty) :
    ∃ U : (Time toRaw V).Opens, U ≤ W ∧ IsIntegral U.toScheme ∧ IsIntegral (Model (inclusion V) U) ∧
      SmoothOfRelativeDimension 1 (openInclusion (inclusion V) U ≫ toBase (inclusion V) (structureMap V) U) ∧
      IsDominant (toBase (inclusion V) (structureMap V) U) ∧ Surjective (toBase (inclusion V) (structureMap V) U) := by
  have : IrreducibleSpace monicBase :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  have : SmoothOfRelativeDimension 1 (inclusion V ≫ structureMap V) := by
    rw [inclusion_over]
    exact timeMap_smooth toRaw V
  exact exists_model (inclusion V) (structureMap V) W hW

end CycleQ2IncidenceIntegralComponent

#print axioms CycleQ2IncidenceIntegralComponent.exists_model
#print axioms CycleQ2IncidenceIntegralComponent.monic_exists_model
