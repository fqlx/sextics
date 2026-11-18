import Proposal.GeometricLiteralMovingPoleComponentsDisjoint
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Gluing the local pole comparison on the three disjoint curves

Each surface point has arbitrarily small framed affine neighborhoods meeting
at most one translated curve. Compatible additive isomorphisms of sections
on these neighborhoods extend to mutually inverse maps of sheaves.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingPoleComponents

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2SeedProjectiveImageCocycle CycleQ2LiteralMovingResidueBasis
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2LiteralOrbitAction CycleQ2LiteralNativeGaugeSections CycleQ2LiteralProjectiveIntersections

structure ComponentPatch extends FramedAffine where
  vertices : Fin 3 → Vertex
  within : ∀ a, carrier ≤ (closedProjectiveAction (rootValues complexRoot a)
    (rootValues_cube complexRoot complexRoot_quadratic a)).hom ⁻¹ᵁ cover (vertices a)
  survivor : Option (Fin 3)
  avoids : ∀ a, survivor ≠ some a → (curveComponent a) ⁻¹ᵁ carrier = ⊥

abbrev componentPatchOpen (W : ComponentPatch) : Surface.Opens := W.carrier

private theorem separatingOpen {X : Type*} [TopologicalSpace X]
    (S : Fin 3 → Set X) (hS : ∀ a, IsClosed (S a))
    (hdisj : Pairwise fun a b => Disjoint (S a) (S b)) (x : X) :
    ∃ (s : Option (Fin 3)) (T : Opens X), x ∈ T ∧
      ∀ a, s ≠ some a → Disjoint (T : Set X) (S a) := by
  classical
  have choice : ∃ s : Option (Fin 3), ∀ a, s ≠ some a → x ∉ S a := by
    by_cases h : ∃ a, x ∈ S a
    · obtain ⟨b,hb⟩ := h
      refine ⟨some b,?_⟩
      intro a ha
      have hba : b ≠ a := fun he => ha (congrArg some he)
      exact Set.disjoint_left.mp (hdisj hba) hb
    · exact ⟨none,fun a _ ha => h ⟨a,ha⟩⟩
  obtain ⟨s,hs⟩ := choice
  let T : Opens X := ⟨(⋃ b : {b : Fin 3 // s ≠ some b}, S b.val)ᶜ,
    (isClosed_iUnion_of_finite (fun b : {b : Fin 3 // s ≠ some b} => hS b.val)).isOpen_compl⟩
  refine ⟨s,T,?_,?_⟩
  · intro h
    obtain ⟨b,hb⟩ := Set.mem_iUnion.mp h
    exact hs b.val b.property hb
  · intro a ha
    exact Set.disjoint_left.mpr fun _ hx hxa => hx (Set.mem_iUnion.mpr ⟨⟨a,ha⟩,hxa⟩)

set_option maxHeartbeats 1200000 in
theorem isBasis_componentPatch : Opens.IsBasis (Set.range componentPatchOpen) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  obtain ⟨s,T,hxT,hT⟩ := separatingOpen (fun a => Set.range (curveComponent a).base)
    (fun a => (curveComponent a).isClosedEmbedding.isClosed_range) components_pairwiseDisjoint x
  obtain ⟨W,v,hxW,hW,hv⟩ := exists_componentNeighborhood (show x ∈ U ⊓ T from ⟨hx,hxT⟩)
  let P : ComponentPatch := ⟨W, v, hv, s, fun a ha => by
    apply le_antisymm _ bot_le
    intro y hy
    have hyW : (curveComponent a).base y ∈ W.carrier := hy
    have hyT : (curveComponent a).base y ∈ T := (hW hyW).2
    exact (Set.disjoint_left.mp (hT a ha) hyT ⟨y,rfl⟩).elim⟩
  exact ⟨W.carrier,⟨P,rfl⟩,hxW,hW.trans inf_le_left⟩

/-- Between different component labels, the smaller open misses all three curves. -/
theorem allOff_of_survivor_ne (W V : ComponentPatch) (h : V.carrier ≤ W.carrier)
    (hne : W.survivor ≠ V.survivor) (a : Fin 3) : (curveComponent a) ⁻¹ᵁ V.carrier = ⊥ := by
  by_cases hv : V.survivor = some a
  · exact le_antisymm ((Scheme.Hom.preimage_mono (curveComponent a) h).trans
      (W.avoids a (fun hw => hne (hw.trans hv.symm))).le) bot_le
  · exact V.avoids a hv

variable {F G : TopCat.Sheaf AddCommGrpCat.{0} (show TopCat from Surface)}

abbrev BasisCompatible (e : (W : ComponentPatch) → F.obj.obj (op W.carrier) ≃+ G.obj.obj (op W.carrier)) : Prop :=
  ∀ (W V : ComponentPatch) (h : V.carrier ≤ W.carrier) (x : F.obj.obj (op W.carrier)),
    e V (F.obj.map (homOfLE h).op x) = G.obj.map (homOfLE h).op (e W x)

private def mapsOnComponents (d : (W : ComponentPatch) → F.obj.obj (op W.carrier) →+ G.obj.obj (op W.carrier))
    (hd : ∀ (W V : ComponentPatch) (h : V.carrier ≤ W.carrier) x,
      d V (F.obj.map (homOfLE h).op x) = G.obj.map (homOfLE h).op (d W x)) :
    (inducedFunctor componentPatchOpen).op ⋙ F.obj ⟶ (inducedFunctor componentPatchOpen).op ⋙ G.obj where
  app W := AddCommGrpCat.ofHom (d W.unop)
  naturality W V j := ConcreteCategory.hom_ext _ _ (hd W.unop V.unop j.unop.hom.le)

private def extendOnComponents (d : (W : ComponentPatch) → F.obj.obj (op W.carrier) →+ G.obj.obj (op W.carrier))
    (hd : ∀ (W V : ComponentPatch) (h : V.carrier ≤ W.carrier) x,
      d V (F.obj.map (homOfLE h).op x) = G.obj.map (homOfLE h).op (d W x)) : F ⟶ G where
  hom := TopCat.Sheaf.restrictHomEquivHom F.obj G isBasis_componentPatch (mapsOnComponents d hd)

private theorem extendOnComponents_apply (d : (W : ComponentPatch) → F.obj.obj (op W.carrier) →+ G.obj.obj (op W.carrier))
    (hd : ∀ (W V : ComponentPatch) (h : V.carrier ≤ W.carrier) x,
      d V (F.obj.map (homOfLE h).op x) = G.obj.map (homOfLE h).op (d W x))
    (W : ComponentPatch) (x : F.obj.obj (op W.carrier)) :
    (extendOnComponents d hd).hom.app (op W.carrier) x = d W x :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app (F := F.obj) (F' := G)
    isBasis_componentPatch (mapsOnComponents d hd) W) x

private theorem inverseCompatible (e : (W : ComponentPatch) → F.obj.obj (op W.carrier) ≃+ G.obj.obj (op W.carrier))
    (he : BasisCompatible e) : BasisCompatible (fun W => (e W).symm) := by
  intro W V h y
  apply (e V).injective
  rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]

/-- A compatible family of section isomorphisms on the single-component basis
identifies the original sheaves on the entire surface. -/
def componentBasisIso (e : (W : ComponentPatch) → F.obj.obj (op W.carrier) ≃+ G.obj.obj (op W.carrier))
    (he : BasisCompatible e) : F ≅ G where
  hom := extendOnComponents (fun W => (e W).toAddMonoidHom) he
  inv := extendOnComponents (fun W => (e W).symm.toAddMonoidHom) (inverseCompatible e he)
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ F isBasis_componentPatch
    intro W
    apply ConcreteCategory.hom_ext
    intro x
    change (extendOnComponents (fun W => (e W).symm.toAddMonoidHom) (inverseCompatible e he)).hom.app (op W.carrier)
      ((extendOnComponents (fun W => (e W).toAddMonoidHom) he).hom.app (op W.carrier) x) = x
    rw [extendOnComponents_apply, extendOnComponents_apply]
    exact (e W).symm_apply_apply x
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ G isBasis_componentPatch
    intro W
    apply ConcreteCategory.hom_ext
    intro x
    change (extendOnComponents (fun W => (e W).toAddMonoidHom) he).hom.app (op W.carrier)
      ((extendOnComponents (fun W => (e W).symm.toAddMonoidHom) (inverseCompatible e he)).hom.app (op W.carrier) x) = x
    rw [extendOnComponents_apply, extendOnComponents_apply]
    exact (e W).apply_symm_apply x

theorem componentBasisIso_apply (e : (W : ComponentPatch) → F.obj.obj (op W.carrier) ≃+ G.obj.obj (op W.carrier))
    (he : BasisCompatible e) (W : ComponentPatch) (x : F.obj.obj (op W.carrier)) :
    (componentBasisIso e he).hom.hom.app (op W.carrier) x = e W x :=
  extendOnComponents_apply _ _ W x

/-- For a target supported on the three components, only equal-label inclusions
require a restriction calculation. -/
theorem compatible_of_same_survivor (e : (W : ComponentPatch) → F.obj.obj (op W.carrier) ≃+ G.obj.obj (op W.carrier))
    (hoff : ∀ V : ComponentPatch, (∀ a, (curveComponent a) ⁻¹ᵁ V.carrier = ⊥) →
      Subsingleton (G.obj.obj (op V.carrier)))
    (hsame : ∀ (W V : ComponentPatch) (h : V.carrier ≤ W.carrier), W.survivor = V.survivor →
      ∀ x, e V (F.obj.map (homOfLE h).op x) = G.obj.map (homOfLE h).op (e W x)) : BasisCompatible e := by
  intro W V h x
  by_cases hs : W.survivor = V.survivor
  · exact hsame W V h hs x
  · let := hoff V (allOff_of_survivor_ne W V h hs)
    exact Subsingleton.elim _ _


section Product

variable {ι : Type} (M : ι → TopCat.Sheaf AddCommGrpCat.{0} (show TopCat from Surface))

private def productProjections (W : Surface.Opens) :
    (∏ᶜ M).obj.obj (op W) →+ (∀ a, (M a).obj.obj (op W)) where
  toFun x a := (Pi.π M a).hom.app (op W) x
  map_zero' := funext fun a => map_zero ((Pi.π M a).hom.app (op W)).hom
  map_add' x y := funext fun a => map_add ((Pi.π M a).hom.app (op W)).hom x y

/-- Sections of the sheaf product are tuples of sections of the factors. -/
def productSectionsEquiv (W : Surface.Opens) :
    (∏ᶜ M).obj.obj (op W) ≃+ (∀ a, (M a).obj.obj (op W)) := by
  let S := sheafToPresheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0} ⋙
    (evaluation _ _).obj (op W)
  let e := (PreservesProduct.iso S M).addCommGroupIsoToAddEquiv.toEquiv.trans
    (Concrete.productEquiv fun i => S.obj (M i))
  apply AddEquiv.ofBijective (productProjections M W)
  have he : ⇑e = ⇑(productProjections M W) := by
    funext x a
    change Concrete.productEquiv (fun i => S.obj (M i)) (piComparison S M x) a = _
    rw [Concrete.productEquiv_apply_apply]
    exact ConcreteCategory.congr_hom (C := AddCommGrpCat) (piComparison_comp_π S M a) x
  rw [← he]
  exact e.bijective

@[simp] theorem productSectionsEquiv_apply (W : Surface.Opens) (x : (∏ᶜ M).obj.obj (op W)) (a : ι) :
    productSectionsEquiv M W x a = (Pi.π M a).hom.app (op W) x := rfl

theorem productSectionsEquiv_restrict {W V : Surface.Opens} (h : V ≤ W)
    (x : (∏ᶜ M).obj.obj (op W)) (a : ι) :
    productSectionsEquiv M V ((∏ᶜ M).obj.map (homOfLE h).op x) a =
      (M a).obj.map (homOfLE h).op (productSectionsEquiv M W x a) :=
  ConcreteCategory.congr_hom (C := AddCommGrpCat) ((Pi.π M a).hom.naturality (homOfLE h).op) x

end Product

end CycleQ2LiteralMovingPoleComponents

end

#print axioms CycleQ2LiteralMovingPoleComponents.componentBasisIso
#print axioms CycleQ2LiteralMovingPoleComponents.compatible_of_same_survivor
#print axioms CycleQ2LiteralMovingPoleComponents.productSectionsEquiv
