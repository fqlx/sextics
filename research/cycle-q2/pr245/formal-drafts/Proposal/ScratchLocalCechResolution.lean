import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! Local quasi-isomorphisms on a cover become quasi-isomorphisms of
the associated complexes of abelian sheaves. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LocalCechResolution
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X : TopCat.{0}} {I : Type*} (U : I → Opens X) (hU : (⨆ i, U i) = ⊤)
abbrev AbPre (X : TopCat.{0}) := (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}
abbrev sheafify (X : TopCat.{0}) := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

private lemma exists_mem (x : X) : ∃ i, x ∈ U i := by
  apply Opens.mem_iSup.mp
  simp [hU]

/-- A presheaf map which is an isomorphism on all opens subordinate to
the cover induces an isomorphism on the associated abelian sheaves. -/
theorem isIso_sheafify_of_cover {F G : AbPre X} (g : F ⟶ G)
    (hg : ∀ (i : I) (V : Opens X), V ≤ U i → IsIso (g.app (op V))) :
    IsIso ((sheafify X).map g) := by
  apply ((Opens.grothendieckTopology X).W_iff g).1
  apply ((Opens.grothendieckTopology X).W_iff_isLocallyBijective g).2
  constructor
  · constructor
    intro W s t hst x hx
    obtain ⟨i, hi⟩ := exists_mem U hU x
    let V := W.unop ⊓ U i
    let j : V ⟶ W.unop := homOfLE inf_le_left
    letI := hg i V inf_le_right
    refine ⟨V, j, ?_, ⟨hx, hi⟩⟩
    change F.map j.op s = F.map j.op t
    apply (ConcreteCategory.bijective_of_isIso (g.app (op V))).1
    simp only [NatTrans.naturality_apply, hst]
  · constructor
    intro W s x hx
    obtain ⟨i, hi⟩ := exists_mem U hU x
    let V := W ⊓ U i
    let j : V ⟶ W := homOfLE inf_le_left
    letI := hg i V inf_le_right
    exact ⟨V, j, (ConcreteCategory.bijective_of_isIso (g.app (op V))).2 (G.map j.op s),
      ⟨hx, hi⟩⟩

private lemma mapShort_quasiIso_iff {A B : Type*} [Category* A] [Abelian A]
    [Category* B] [Abelian B] (E : A ⥤ B) [E.Additive] [E.PreservesHomology]
    {S T : ShortComplex A} (g : S ⟶ T) :
    ShortComplex.QuasiIso (E.mapShortComplex.map g) ↔ IsIso (E.map (ShortComplex.homologyMap g)) := by
  rw [ShortComplex.quasiIso_iff]
  exact (MorphismProperty.isomorphisms B).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso E)).app (Arrow.mk g))

/-- Sheafification sends a map of complexes of additive presheaves to a
quasi-isomorphism if evaluation at every cover-subordinate open does. -/
theorem quasiIso_sheafify_of_cover {J : Type*} {c : ComplexShape J}
    {K L : HomologicalComplex (AbPre X) c} (f : K ⟶ L)
    (hf : ∀ (i : I) (V : Opens X), V ≤ U i →
      QuasiIso (((((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op V)).mapHomologicalComplex c).map f))) :
    QuasiIso (((sheafify X).mapHomologicalComplex c).map f) := by
  constructor
  intro n
  rw [quasiIsoAt_iff]
  let g := (HomologicalComplex.shortComplexFunctor (AbPre X) c n).map f
  apply (mapShort_quasiIso_iff (sheafify X) g).2
  apply isIso_sheafify_of_cover U hU
  intro i V hi
  let E := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op V)
  have h := (quasiIso_iff _).1 (hf i V hi) n
  rw [quasiIsoAt_iff] at h
  exact (mapShort_quasiIso_iff E g).1 h

end CycleQ2LocalCechResolution
#print axioms CycleQ2LocalCechResolution.quasiIso_sheafify_of_cover
