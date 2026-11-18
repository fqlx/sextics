import Proposal.GeometricLiteralTimeNormalizationRegular
import Proposal.GeometricNormalCurveSmooth

/-!
# Smoothness of the normalized fixed-sextic time branch

The affine neighborhoods over the completion have Dedekind coordinate rings.
They are smooth over the perfect field of complex numbers. Every standard
smooth chart meets the dense original open, where the relative dimension
is one. Uniqueness of smooth dimension on that intersection gives dimension
one everywhere on the normalized branch.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeNormalizationSmooth

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralTimeCurveCompletion
  CycleQ2LiteralTimeCurveNormalization CycleQ2SweptSupport

variable (U : Curve.Opens) [IsAffine U.toScheme] [AlgebraicGeometry.IsIntegral U.toScheme]

/-- The entire normalized parameter branch is smooth over the complex point. -/
theorem smooth : Smooth (toComplexPoint U) := by
  let f := toComplexPoint U
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, _⟩ :=
    (Completion U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (toCompletion U x)) isOpen_univ
  let T := toCompletion U ⁻¹ᵁ V
  let hT : IsAffineOpen T := hV.preimage (toCompletion U)
  let A := Γ(Normalization U,T)
  let hle : T ≤ f ⁻¹ᵁ ⊤ := by simp
  let c := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ T hle
  let : Algebra ℂ A := c.hom.toAlgebra
  have : IsDedekindDomain A := CycleQ2LiteralTimeNormalizationRegular.preimage_dedekind U hV x hx
  have : Algebra.FiniteType ℂ A := (f.finiteType_appLE (isAffineOpen_top _) hT hle).comp
    (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  have hc : Spec.map c = hT.fromSpec ≫ f := by
    rw [Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hT hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have : Smooth (hT.fromSpec ≫ f) := by
    rw [← hc]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (CycleQ2NormalCurveSmooth.smooth_of_isDedekindDomain
        (K := ℂ) (A := A)))
  obtain ⟨q, hq⟩ : x ∈ Set.range hT.fromSpec := by rw [hT.range_fromSpec]; exact hx
  rw [← hq]
  change q ∈ hT.fromSpec ⁻¹ᵁ f.smoothLocus
  rw [hT.fromSpec.preimage_smoothLocus_eq f, Scheme.Hom.smoothLocus_eq_top]
  exact Set.mem_univ _

private theorem dimension_eq {Y : Scheme.{0}} [NoetherianSpace Y] (y : Y)
    (f : Y ⟶ Spec (CommRingCat.of ℂ)) (a b : ℕ)
    [SmoothOfRelativeDimension a f] [SmoothOfRelativeDimension b f] : a = b := by
  have hd : DenseRange (𝟙 Y : Y ⟶ Y) := by
    change DenseRange (id : Y → Y)
    exact denseRange_id
  have aux (m n : ℕ) [SmoothOfRelativeDimension m f] [SmoothOfRelativeDimension n f] :
      ¬ m < n := fun h => closure_range_ne_univ m n h f f y (𝟙 Y) (Category.id_comp _)
        hd.closure_eq
  exact Nat.le_antisymm (Nat.le_of_not_gt (aux b a)) (Nat.le_of_not_gt (aux a b))

private theorem relativeDimension_of_dense_open {X Y : Scheme.{0}} [NoetherianSpace Y]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j] (f : X ⟶ Spec (CommRingCat.of ℂ))
    [Smooth f] [SmoothOfRelativeDimension 1 (j ≫ f)] : SmoothOfRelativeDimension 1 f := by
  constructor
  intro x
  obtain ⟨O,hO,V,hV,hx,hle,hs⟩ := Smooth.exists_isStandardSmooth (f := f) x
  have hOtop : O = ⊤ := by
    apply top_unique
    intro z _
    exact Subsingleton.elim (f x) z ▸ hle hx
  subst O
  let A := Γ(X, V)
  let l := (f.appLE ⊤ V hle).hom
  let : Algebra Γ(Spec (CommRingCat.of ℂ), ⊤) A := l.toAlgebra
  have hs' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of ℂ), ⊤) A := hs
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hs'.out
  let n := P.dimension
  have hn : l.IsStandardSmoothOfRelativeDimension n := P.isStandardSmoothOfRelativeDimension rfl
  let c := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ V hle
  have hc : Spec.map c = hV.fromSpec ≫ f := by
    rw [Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hstd : c.hom.IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have : SmoothOfRelativeDimension n (hV.fromSpec ≫ f) := by
    rw [← hc]
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mpr
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hstd
  let W := j ⁻¹ᵁ V
  let t : W.toScheme ⟶ Spec A := CycleQ2DenseOpenAffineSections.chart j hV
  let p := W.ι ≫ j ≫ f
  have htp : t ≫ hV.fromSpec ≫ f = p := by
    change ((j ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.fromSpec ≫ f = _
    simp only [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc, Category.assoc,
      morphismRestrict_ι_assoc, p, W]
  have : SmoothOfRelativeDimension n p := by
    rw [← htp]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 n t (hV.fromSpec ≫ f)
  have : SmoothOfRelativeDimension 1 p := smoothOfRelativeDimension_comp 0 1 W.ι (j ≫ f)
  let : NoetherianSpace W.toScheme := NoetherianSpace.set (W : Set Y)
  obtain ⟨y, hy⟩ := j.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
  have hn1 := dimension_eq (Y := W.toScheme) ⟨y,hy⟩ p n 1
  exact ⟨⊤, hO, V, hV, hx, hle, hn1 ▸ hn⟩

/-- The proper normalized branch is a smooth complex curve of relative dimension one,
including the points outside its original parameter open. -/
theorem smooth_curve : SmoothOfRelativeDimension 1 (toComplexPoint U) := by
  let : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set Curve)
  have := smooth U
  have := smooth_on_original_open U
  exact relativeDimension_of_dense_open (openInclusion U) (toComplexPoint U)

#print axioms smooth
#print axioms smooth_curve

end CycleQ2LiteralTimeNormalizationSmooth
end
