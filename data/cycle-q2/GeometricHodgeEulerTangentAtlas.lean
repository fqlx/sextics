import Proposal.GeometricChartSectionPullback
import Proposal.GeometricHodgeEulerTangentSheaf

/-!
# Affine charts on the image of a complex affine open immersion

The full chart and its principal subcharts commute with the morphism
to the base. Their function-ring isomorphisms carry a ring element
to its restriction in the original structure sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerTangentAtlas

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricAffineChartSections CycleQ2ChartSectionPullback
open CycleQ2HodgeEulerTangentSheaf (functions functions_apply)

variable {A : Type} [CommRing A] {X : Scheme.{0}}
  (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]

def topChart : (j ''ᵁ ⊤).toScheme ≅ Spec (CommRingCat.of A) :=
  (j.isoImage ⊤).symm ≪≫ (Spec (CommRingCat.of A)).topIso

def basicChart (z : A) : (j ''ᵁ PrimeSpectrum.basicOpen z).toScheme ≅
    Spec (CommRingCat.of (Localization.Away z)) :=
  (j.isoImage _).symm ≪≫ basicOpenIsoSpecAway (R := CommRingCat.of A) z

@[reassoc] theorem topChart_inv_ι :
    (topChart j).inv ≫ (j ''ᵁ ⊤).ι = j := by
  simp only [topChart, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Scheme.Hom.isoImage_hom_ι, Scheme.toIso_inv_ι_assoc]

@[reassoc] theorem basicChart_inv_ι (z : A) :
    (basicChart j z).inv ≫ (j ''ᵁ PrimeSpectrum.basicOpen z).ι =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away z))) ≫ j := by
  have h := basicOpenIsoSpecAway_hom_SpecMap_assoc (R := CommRingCat.of A) z j
  simp only [basicChart, Iso.trans_inv, Iso.symm_inv, Category.assoc, Scheme.Hom.isoImage_hom_ι]
  rw [← h, Iso.inv_hom_id_assoc]

section OverBase

variable [Algebra ℂ A] (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

include h in
theorem topChart_overBase :
    (topChart j).inv ≫ (j ''ᵁ ⊤).ι ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) := by
  rw [topChart_inv_ι_assoc, h]

include h in
theorem basicChart_overBase (z : A) :
    (basicChart j z).inv ≫ (j ''ᵁ PrimeSpectrum.basicOpen z).ι ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away z))) := by
  rw [← Category.assoc, basicChart_inv_ι, Category.assoc, h, ← Spec.map_comp]
  exact congrArg (fun q : ℂ →+* Localization.Away z => Spec.map (CommRingCat.ofHom q))
    (IsScalarTower.algebraMap_eq ℂ A (Localization.Away z)).symm

end OverBase

variable {B : Type} [CommRing B]

private theorem image_functions (V : (Spec (CommRingCat.of A)).Opens)
    (e : V.toScheme ≅ Spec (CommRingCat.of B)) (b : B) :
    functions ((j.isoImage V).symm ≪≫ e) b = (j.appIso V).inv (functions e b) := by
  have h : e.inv ≫ V.ι ≫ j = Spec.map (CommRingCat.ofHom (RingHom.id B)) ≫
      ((j.isoImage V).symm ≪≫ e).inv ≫ (j ''ᵁ V).ι := by
    change _ = Spec.map (𝟙 (CommRingCat.of B)) ≫ _
    simp only [Spec.map_id, Category.id_comp, Iso.trans_inv, Iso.symm_inv,
      Category.assoc, Scheme.Hom.isoImage_hom_ι]
  rw [functions_apply, functions_apply]
  apply (j.appIso V).commRingCatIsoToRingEquiv.injective
  change (j.appIso V).hom _ = (j.appIso V).hom ((j.appIso V).inv _)
  rw [Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom']
  exact chartSection_pullback_top j _ e (RingHom.id B) _ h b

private theorem intrinsic_scalar (V : (Spec (CommRingCat.of A)).Opens)
    (e : V.toScheme ≅ Spec (CommRingCat.of B)) (ρ : A →+* B)
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom ρ) = V.ι) (a : A) :
    functions e (ρ a) =
      (Spec (CommRingCat.of A)).presheaf.map V.leTop.op ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := by
  have hr : V.ι.appTop ≫ V.topIso.hom = (Spec (CommRingCat.of A)).presheaf.map V.leTop.op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    exact congrArg (Spec (CommRingCat.of A)).presheaf.map (Subsingleton.elim _ _)
  have h : CommRingCat.ofHom ρ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ e.hom.appTop ≫ V.topIso.hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec (CommRingCat.of A)).presheaf.map V.leTop.op := by
    calc
      _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (e.hom ≫ Spec.map (CommRingCat.ofHom ρ)).appTop ≫
          V.topIso.hom := by
        simp only [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.comp_appTop, Category.assoc]
      _ = _ := by rw [he, hr]
  exact ConcreteCategory.congr_hom h a

theorem functions_topChart (a : A) :
    functions (topChart j) a = (j.appIso ⊤).inv ((Spec (CommRingCat.of A)).presheaf.map
      (⊤ : (Spec (CommRingCat.of A)).Opens).leTop.op ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) := by
  rw [topChart, image_functions]
  apply congrArg (j.appIso ⊤).inv
  exact intrinsic_scalar _ (Spec (CommRingCat.of A)).topIso (RingHom.id A)
    (by
      change (Spec (CommRingCat.of A)).topIso.hom ≫ Spec.map (𝟙 (CommRingCat.of A)) = _
      simp only [Scheme.topIso_hom, Spec.map_id, Category.comp_id]) a

theorem functions_basicChart (z a : A) :
    functions (basicChart j z) (algebraMap A (Localization.Away z) a) =
      (j.appIso _).inv ((Spec (CommRingCat.of A)).presheaf.map
        (PrimeSpectrum.basicOpen z).leTop.op ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) := by
  rw [basicChart, image_functions]
  apply congrArg (j.appIso _).inv
  exact intrinsic_scalar (A := A) (B := Localization.Away z) (PrimeSpectrum.basicOpen z)
    (basicOpenIsoSpecAway (R := CommRingCat.of A) z) (algebraMap A (Localization.Away z))
    (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) z) a

/-- The restriction from the full chart to a principal open is localization
on the affine coordinates of the original structure sheaf. -/
theorem restrict_topChart_basicChart (z a : A) :
    X.presheaf.map (homOfLE (j.image_mono (show PrimeSpectrum.basicOpen z ≤ ⊤ from le_top))).op
        (functions (topChart j) a) =
      functions (basicChart j z) (algebraMap A (Localization.Away z) a) := by
  rw [functions_topChart, functions_basicChart]
  have hid : (⊤ : (Spec (CommRingCat.of A)).Opens).leTop.op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [hid, (Spec (CommRingCat.of A)).presheaf.map_id (op (⊤ : (Spec (CommRingCat.of A)).Opens))]
  exact ConcreteCategory.congr_hom
    (j.appIso_inv_naturality (PrimeSpectrum.basicOpen z).leTop.op).symm
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)

end CycleQ2HodgeEulerTangentAtlas
end

#print axioms CycleQ2HodgeEulerTangentAtlas.functions_topChart
#print axioms CycleQ2HodgeEulerTangentAtlas.functions_basicChart
