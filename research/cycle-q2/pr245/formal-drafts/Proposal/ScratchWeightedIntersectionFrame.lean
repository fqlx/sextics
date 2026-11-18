import Proposal.ScratchWeightedResidueAtlas
import Proposal.ScratchCechSchemeSectionAlgebras
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Kaehler

/-! Exact coordinates on affine intersections of the gradient atlas.
The map from a native gradient patch into the structure sections of any
affine subopen is étale, because its Spec is the actual open immersion.
This base changes the existing rank-three Kähler basis to the intersection.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open CategoryTheory AlgebraicGeometry Module
open CycleQ2.Cech.Sections CycleQ2WeightedResidueAtlas CycleQ2HodgeEuler
  CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerChartDerivations
  CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient
open scoped KaehlerDifferential
namespace CycleQ2WeightedIntersectionFrame
variable {k : Type} [CommRing k]

theorem baseMap_spec {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k)) {W : X.Opens}
    (hW : IsAffineOpen W) : Spec.map (CommRingCat.ofHom (baseMap f W)) = hW.fromSpec ≫ f := by
  apply (cancel_epi hW.isoSpec.hom).mp
  change W.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso _).inv ≫ f.appTop ≫ X.presheaf.map W.leTop.op) = _
  simp only [Spec.map_comp,← Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  simp only [Category.assoc,← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id,IsAffineOpen.isoSpec_hom_fromSpec_assoc]

variable (φ : CoeffRing →+* k) (a : Index) {W : (threefold φ).Opens}
    (hW : IsAffineOpen W) (h : W ≤ U φ a)
abbrev Model := Patch (F φ a.1) a.2

def patchMapToSection : Model φ a →+* Γ(threefold φ,W) :=
  (Spec.preimage (hW.isoSpec.inv ≫ (threefold φ).homOfLE h ≫ (atlas φ a).hom)).hom

theorem patch_etale : (patchMapToSection φ a hW h).Etale := by
  apply (HasRingHomProperty.Spec_iff (P:=@Etale)).mp
  change Etale (Spec.map (Spec.preimage _))
  rw [Spec.map_preimage]
  infer_instance

theorem patch_overBase : baseMap (toBase φ) W =
    (patchMapToSection φ a hW h).comp (algebraMap k (Model φ a)) := by
  have eq : CommRingCat.ofHom (baseMap (toBase φ) W) =
      CommRingCat.ofHom (algebraMap k (Model φ a)) ≫
        Spec.preimage (hW.isoSpec.inv ≫ (threefold φ).homOfLE h ≫ (atlas φ a).hom) := by
    apply Spec.map_injective
    rw [baseMap_spec _ hW, Spec.map_comp,Spec.map_preimage,← atlas_overBase φ a]
    simp only [Category.assoc,Iso.hom_inv_id_assoc,Scheme.homOfLE_ι_assoc,
      IsAffineOpen.isoSpec_inv_ι_assoc]
  exact congrArg CommRingCat.Hom.hom eq

theorem exact_frame :
    letI := algebra (toBase φ) W
    ∃ (x : Fin 3 → Γ(threefold φ,W)) (b : Basis (Fin 3) Γ(threefold φ,W) Ω[Γ(threefold φ,W)⁄k]),
      ∀ i, b i = KaehlerDifferential.D k _ (x i) := by
  letI := algebra (toBase φ) W
  letI := (patchMapToSection φ a hW h).toAlgebra
  letI : IsScalarTower k (Model φ a) Γ(threefold φ,W) :=
    IsScalarTower.of_algebraMap_eq' (patch_overBase φ a hW h)
  letI : Algebra.Etale (Model φ a) Γ(threefold φ,W) := (patch_etale φ a hW h).toAlgebra
  let q := F φ a.1
  let j := a.2
  let x (i : Fin 3) : Model φ a := patchMap q j (mk q (MvPolynomial.X (j.succAbove i)))
  refine ⟨fun i => algebraMap (Model φ a) Γ(threefold φ,W) (x i),
    ((basis q j).baseChange Γ(threefold φ,W)).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (Model φ a) Γ(threefold φ,W)), ?_⟩
  intro i
  simp only [Basis.map_apply,Basis.baseChange_apply,basis_apply]
  change KaehlerDifferential.mapBaseChange k (Model φ a) Γ(threefold φ,W) _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul,one_smul,KaehlerDifferential.map_D]

theorem simplex_frame {I : Type*} [Finite I] [Nonempty I] (v : I → Index) :
    let W := ⨅ i, U φ (v i)
    letI := algebra (toBase φ) W
    ∃ (x : Fin 3 → Γ(threefold φ,W)) (b : Basis (Fin 3) Γ(threefold φ,W) Ω[Γ(threefold φ,W)⁄k]),
      ∀ i, b i = KaehlerDifferential.D k _ (x i) :=
  let i : I := Classical.choice inferInstance
  exact_frame φ (v i) (finite_affine φ v) (iInf_le _ i)

end CycleQ2WeightedIntersectionFrame
end
#print axioms CycleQ2WeightedIntersectionFrame.patch_etale
#print axioms CycleQ2WeightedIntersectionFrame.simplex_frame
