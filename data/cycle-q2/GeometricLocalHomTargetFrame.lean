import Proposal.GeometricNormalSheafComparison
import Proposal.GeometricCanonicalGluing

/-!
# Changing the target frame of a sheaf of linear maps

An actual linear frame on a patch acts on the target of every local
linear map there. These maps give a linear isomorphism of local sheaves
and commute with restriction to every smaller open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LocalHomTargetFrame
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricModuleLocalIso
variable {X : Scheme.{0}} (M : X.Modules) {A B : X.Modules} {U W : X.Opens}
  (e : PatchIso A B U) (hW : W ≤ U)

def post (s : LocalLinearHom X.sheaf M A W) : LocalLinearHom X.sheaf M B W := by
  refine ⟨{ app := fun V => s.val.app V ≫ AddCommGrpCat.ofHom (e.app V.unop.left (V.unop.hom.le.trans hW)).toAddMonoidHom
            naturality := ?_ }, ?_⟩
  · intro V Q h
    apply ConcreteCategory.hom_ext
    intro m
    change e.app Q.unop.left _ (s.val.app Q (M.val.map h.unop.left.op m)) =
      B.val.map h.unop.left.op (e.app V.unop.left _ (s.val.app V m))
    have hs := ConcreteCategory.congr_hom (s.val.naturality h) m
    change s.val.app Q (M.val.map h.unop.left.op m) = A.val.map h.unop.left.op (s.val.app V m) at hs
    rw [hs]
    exact (e.naturality h.unop.left.le (V.unop.hom.le.trans hW) _).symm
  · intro V r m
    change e.app V.left _ (s.val.app (op V) (r • m)) = r • e.app V.left _ (s.val.app (op V) m)
    rw [s.property, map_smul]

/-- The full sectionwise linear equivalence of internal Hom sheaves on a patch. -/
def postFrame : PatchIso (moduleHomSheaf X.sheaf M A) (moduleHomSheaf X.sheaf M B) U where
  app W hW := {
    toFun := post M e hW
    invFun := post M e.symm hW
    left_inv := fun s => by
      apply localLinearHom_ext
      intro V m
      exact (e.app V.left _).symm_apply_apply _
    right_inv := fun s => by
      apply localLinearHom_ext
      intro V m
      exact (e.app V.left _).apply_symm_apply _
    map_add' := fun s q => by
      apply localLinearHom_ext
      intro V m
      exact (e.app V.left _).map_add _ _
    map_smul' := fun r s => by
      apply localLinearHom_ext
      intro V m
      exact (e.app V.left _).map_smul _ _ }
  naturality h hW s := by
    apply localLinearHom_ext
    intro V m
    rfl

theorem postFrame_apply (s : LocalLinearHom X.sheaf M A W) (V : Over W) (m : M.val.obj (op V.left)) :
    ((postFrame M e).app W hW s).val.app (op V) m = e.app V.left (V.hom.le.trans hW) (s.val.app (op V) m) := rfl

end CycleQ2LocalHomTargetFrame
end

#print axioms CycleQ2LocalHomTargetFrame.postFrame
