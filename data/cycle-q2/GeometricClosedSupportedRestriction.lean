import Proposal.GeometricClosedEmbeddingSheafExact
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# An additive sheaf supported on a closed subspace

The inverse-image sheaf is obtained by sheafifying the presheaf pullback.
The canonical map to its direct image is an isomorphism on the closed
subspace. If the source stalks vanish on the complement it is an isomorphism
on the entire ambient space.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ClosedSupportedRestriction
open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite
  TopCat.Presheaf CycleQ2ClosedEmbeddingSheafExact CycleQ2ClosedSupportCohomology

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

abbrev inverseSheaf (F : Y.Sheaf AddCommGrpCat.{0}) : X.Sheaf AddCommGrpCat.{0} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    ((TopCat.Presheaf.pullback AddCommGrpCat f).obj F.obj)

/-- This explicit sheafification is the usual inverse image of additive sheaves. -/
def inverseSheafIso (F : Y.Sheaf AddCommGrpCat.{0}) :
    (TopCat.Sheaf.pullback AddCommGrpCat f).obj F ≅ inverseSheaf f F :=
  (TopCat.Sheaf.pullbackIso AddCommGrpCat f).app F

def supportUnit (F : Y.Sheaf AddCommGrpCat.{0}) : F ⟶ (push f).obj (inverseSheaf f F) where
  hom := (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app F.obj ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat f).map
      (toSheafify (Opens.grothendieckTopology X) _)

private theorem stalkPushforward_natural {A B : X.Presheaf AddCommGrpCat.{0}} (k : A ⟶ B) (x : X) :
    (stalkFunctor AddCommGrpCat (f x)).map ((TopCat.Presheaf.pushforward AddCommGrpCat f).map k) ≫
      B.stalkPushforward AddCommGrpCat f x =
    A.stalkPushforward AddCommGrpCat f x ≫ (stalkFunctor AddCommGrpCat x).map k := by
  apply stalk_hom_ext
  intro U hU
  simp

private theorem isIso_unit_at (hf : IsClosedEmbedding f) (F : Y.Sheaf AddCommGrpCat.{0}) (x : X) :
    IsIso ((stalkFunctor AddCommGrpCat (f x)).map (supportUnit f F).hom) := by
  classical
  let P := (TopCat.Presheaf.pullback AddCommGrpCat f).obj F.obj
  let k := toSheafify (Opens.grothendieckTopology X) P
  let g := stalkPushforward AddCommGrpCat f (inverseSheaf f F).obj x
  have : IsIso g := stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat hf.isInducing _ x
  have he : (stalkFunctor AddCommGrpCat (f x)).map (supportUnit f F).hom ≫ g =
      (stalkPullbackIso AddCommGrpCat f F.obj x).hom ≫ (stalkFunctor AddCommGrpCat x).map k := by
    change (stalkFunctor AddCommGrpCat (f x)).map (_ ≫ (TopCat.Presheaf.pushforward AddCommGrpCat f).map k) ≫ g = _
    rw [Functor.map_comp, Category.assoc, stalkPushforward_natural f k, ← Category.assoc]
    rfl
  have : IsIso ((stalkFunctor AddCommGrpCat x).map k) :=
    Adjunction.isIso_map_unit_of_isLeftAdjoint_comp (sheafificationAdjunction _ AddCommGrpCat)
      (skyscraperSheafForgetAdjunction x)
  have : IsIso ((stalkFunctor AddCommGrpCat (f x)).map (supportUnit f F).hom ≫ g) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ g

theorem stalk_subsingleton_of_sections {F : Y.Sheaf AddCommGrpCat.{0}} {y : Y}
    {U : Opens Y} (hy : y ∈ U) (h : ∀ W ≤ U, Subsingleton (F.obj.obj (op W))) :
    Subsingleton (stalk (C := AddCommGrpCat) F.obj y) := by
  have hzero (a : stalk (C := AddCommGrpCat) F.obj y) : a = 0 := by
    obtain ⟨V,hV,s,rfl⟩ := exists_germ_eq F.obj a
    let W := V ⊓ U
    have hz := (h W inf_le_right).elim (F.obj.map (homOfLE (show W ≤ V from inf_le_left)).op s) 0
    rw [← germ_res_apply F.obj (homOfLE (show W ≤ V from inf_le_left)) y (show y ∈ W from ⟨hV,hy⟩),
      hz, map_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

private theorem push_stalk_subsingleton (hf : IsClosedEmbedding f) (F : X.Sheaf AddCommGrpCat.{0})
    {y : Y} (hy : y ∉ Set.range f) : Subsingleton (stalk (C := AddCommGrpCat) ((push f).obj F).obj y) := by
  let U := extendedOpen f hf ⊥
  have hu : y ∈ U := fun ⟨x,_,hx⟩ => hy ⟨x,hx⟩
  apply stalk_subsingleton_of_sections (F := (push f).obj F) hu
  intro W hW
  have he : (Opens.map f).obj W = ⊥ :=
    le_antisymm (((Opens.map f).map (homOfLE hW)).le.trans (preimage_extendedOpen f hf ⊥).le) bot_le
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (F.isTerminalOfEqEmpty he).isZero

/-- The inverse-image unit induces an isomorphism at each point of the embedded subspace. -/
theorem supportUnit_stalk_isIso (hf : IsClosedEmbedding f) (F : Y.Sheaf AddCommGrpCat.{0}) (x : X) :
    IsIso ((stalkFunctor AddCommGrpCat (f x)).map (supportUnit f F).hom) :=
  isIso_unit_at f hf F x

/-- The direct image under a closed embedding has zero stalks on its complement. -/
theorem push_stalk_off_range (hf : IsClosedEmbedding f) (F : X.Sheaf AddCommGrpCat.{0})
    {y : Y} (hy : y ∉ Set.range f) : Subsingleton (stalk (C := AddCommGrpCat) ((push f).obj F).obj y) :=
  push_stalk_subsingleton f hf F hy

/-- The canonical map identifies a sheaf with the direct image of its inverse image
once all stalks off the closed subset are zero. -/
def supportedIso (hf : IsClosedEmbedding f) (F : Y.Sheaf AddCommGrpCat.{0})
    (h : ∀ y ∉ Set.range f, Subsingleton (stalk (C := AddCommGrpCat) F.obj y)) : F ≅ (push f).obj (inverseSheaf f F) := by
  have : IsIso (supportUnit f F) := by
    apply (isIso_iff_stalkFunctor_map_iso _).mpr
    intro y
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x,rfl⟩ := hy
      exact isIso_unit_at f hf F x
    · let z := AddCommGrpCat.isZero_iff_subsingleton.mpr (h y hy)
      let z' := AddCommGrpCat.isZero_iff_subsingleton.mpr (push_stalk_subsingleton f hf (inverseSheaf f F) hy)
      rw [z.eq_of_src ((stalkFunctor AddCommGrpCat y).map (supportUnit f F).hom) (z.iso z').hom]
      infer_instance
  exact asIso (supportUnit f F)

end CycleQ2ClosedSupportedRestriction
end

#print axioms CycleQ2ClosedSupportedRestriction.supportedIso
