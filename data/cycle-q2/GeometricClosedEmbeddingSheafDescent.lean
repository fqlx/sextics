import Proposal.GeometricClosedSupportedRestriction
import Proposal.GeometricClosedEmbeddingCohomology

/-!
# Descent of additive sheaf isomorphisms across a closed embedding

A morphism between the two direct images can be evaluated on the
extension of each open subset by the whole complement. Restricting to
these opens recovers the original sheaves and preserves isomorphisms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ClosedEmbeddingSheafDescent
open CategoryTheory Topology TopologicalSpace Opposite
  CycleQ2ClosedEmbeddingSheafExact CycleQ2ClosedSupportCohomology

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsClosedEmbedding f)

def extension : Opens X ⥤ Opens Y where
  obj := extendedOpen f hf
  map h := homOfLE (extendedOpen_mono f hf h.le)

/-- Evaluating a direct image on the extended opens recovers the whole presheaf. -/
def extendPushIso (F : X.Sheaf AddCommGrpCat.{0}) :
    (extension f hf).op ⋙ ((push f).obj F).obj ≅ F.obj :=
  NatIso.ofComponents (fun U => (pushedSectionsEquiv f hf F U.unop).toAddCommGrpIso)
    (by
      intro U V h
      ext a
      exact pushedSectionsEquiv_restrict f hf F h.unop.le a)

def unpushHom {F G : X.Sheaf AddCommGrpCat.{0}} (p : (push f).obj F ⟶ (push f).obj G) :
    F ⟶ G where
  hom := (extendPushIso f hf F).inv ≫ Functor.whiskerLeft (extension f hf).op p.hom ≫
    (extendPushIso f hf G).hom

/-- An actual isomorphism on the closed subspace descended from its direct image. -/
def unpushIso {F G : X.Sheaf AddCommGrpCat.{0}} (e : (push f).obj F ≅ (push f).obj G) :
    F ≅ G :=
  ObjectProperty.isoMk _ ((extendPushIso f hf F).symm ≪≫
    Functor.isoWhiskerLeft (extension f hf).op ((sheafToPresheaf _ _).mapIso e) ≪≫
      extendPushIso f hf G)

theorem unpushIso_hom {F G : X.Sheaf AddCommGrpCat.{0}} (e : (push f).obj F ≅ (push f).obj G) :
    (unpushIso f hf e).hom = unpushHom f hf e.hom := rfl

private theorem le_extended_preimage (V : Opens Y) :
    V ≤ extendedOpen f hf ((Opens.map f).obj V) := by
  rintro y hy ⟨x,hx,rfl⟩
  exact hx hy

private theorem res_from_extended (F : X.Sheaf AddCommGrpCat.{0}) (V : Opens Y)
    (a : ((push f).obj F).obj.obj (op (extendedOpen f hf ((Opens.map f).obj V)))) :
    ((push f).obj F).obj.map (homOfLE (le_extended_preimage f hf V)).op a =
      pushedSectionsEquiv f hf F ((Opens.map f).obj V) a := by
  change F.obj.map _ a = F.obj.map _ a
  congr 1

theorem push_unpushHom {F G : X.Sheaf AddCommGrpCat.{0}} (p : (push f).obj F ⟶ (push f).obj G) :
    (push f).map (unpushHom f hf p) = p := by
  apply ObjectProperty.hom_ext
  ext V a
  let U := (Opens.map f).obj V.unop
  let s := (pushedSectionsEquiv f hf F U).symm a
  have h := congrArg (fun l : ((push f).obj F).obj.obj (op (extendedOpen f hf U)) ⟶
      ((push f).obj G).obj.obj V => l s)
    (p.hom.naturality (homOfLE (le_extended_preimage f hf V.unop)).op)
  change p.hom.app V (((push f).obj F).obj.map _ s) =
    ((push f).obj G).obj.map _ (p.hom.app _ s) at h
  rw [res_from_extended, res_from_extended] at h
  change pushedSectionsEquiv f hf G U (p.hom.app (op (extendedOpen f hf U)) s) = p.hom.app V a
  simpa only [s, U, AddEquiv.apply_symm_apply] using h.symm

open CategoryTheory.Abelian CycleQ2ClosedEmbeddingCohomology
local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- Direct-image comparison commutes with the map in cohomology of every
morphism on the closed subspace. -/
theorem pushHEquiv_natural {F G : X.Sheaf AddCommGrpCat.{0}}
    (p : F ⟶ G) (n : ℕ) (x : F.H' n ⊤) :
    pushHEquiv f hf G n (x.comp (Ext.mk₀ p) (add_zero n)) =
      (pushHEquiv f hf F n x).comp (Ext.mk₀ ((push f).map p)) (add_zero n) := by
  let := push_preservesFiniteColimits f hf
  let := push_preservesInjectiveObjects f
  change (Ext.mk₀ _).comp ((x.comp (Ext.mk₀ p) (add_zero n)).mapExactFunctor (push f)) (zero_add n) =
    ((Ext.mk₀ _).comp (x.mapExactFunctor (push f)) (zero_add n)).comp (Ext.mk₀ ((push f).map p)) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

end CycleQ2ClosedEmbeddingSheafDescent
end

#print axioms CycleQ2ClosedEmbeddingSheafDescent.unpushIso
