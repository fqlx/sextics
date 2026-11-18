import Proposal.GeometricHodgeEulerContractionSheaf
import Proposal.GeometricSurfaceResidueFunctoriality

/-!
# Gluing the local contraction isomorphisms

Whenever generating frames for a single volume give an isomorphism on
each member of a cover, these isomorphisms agree on all intersections.
Their glued map evaluates on every open by contraction with the original
volume. The inverse glues by the sheaf property as well.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeVolumeContraction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2HodgeEulerContractionSheaf
  CycleQ2GeometricModuleLocalIso CycleQ2LocalFrameGluing

variable {X : Scheme.{0}} {M N : X.Modules} {U : X.Opens}

private def asPatch (s : M.over U ≅ N.over U) : PatchIso M N U where
  app W hW := ((SheafOfModules.evaluation ((ringSheaf X.sheaf).over U)
    (op (Over.mk (homOfLE hW)))).mapIso s).toLinearEquiv
  naturality {O W} a hO x := by
    let k : Over.mk (homOfLE (a.trans hO)) ⟶ Over.mk (homOfLE hO) := Over.homMk (homOfLE a)
    exact (PresheafOfModules.naturality_apply s.hom.val k.op x).symm

variable (M) (ω : (form M 3).val.obj (op ⊤)) {I : Type} (D : I → X.Opens)
  (cover : (⨆ i, D i) = ⊤) (s : ∀ i, (dual M).over (D i) ≅ (form M 2).over (D i))
  (hs : ∀ (i) (W : X.Opens) (hi : W ≤ D i) (v : (dual M).val.obj (op W)),
    (s i).hom.val.app (op (Over.mk (homOfLE hi))) v = contractSection M W v
      ((form M 3).val.map (homOfLE (le_top : W ≤ ⊤)).op ω))

include hs in
private theorem compatible (i j : I) : (asPatch (s i)).Compatible (asPatch (s j)) := by
  intro O hi hj v
  exact (hs i O hi v).trans (hs j O hj v).symm

include cover hs in
def gluedIso : dual M ≅ form M 2 := by
  let p := Cover.gluePatchIso (dual M) (form M 2) ⊤ D cover.ge (fun i => asPatch (s i))
    (compatible M ω D s hs)
  exact glueIso _ _ ⊤ ⊤ (by simp) p p (fun _ _ _ _ => rfl)

include cover hs in
private theorem gluedIso_patch (i : I) (W : X.Opens) (hW : W ≤ D i)
    (v : (dual M).val.obj (op W)) :
    (gluedIso M ω D cover s hs).hom.val.app (op W) v =
      contractSection M W v ((form M 3).val.map (homOfLE (le_top : W ≤ ⊤)).op ω) := by
  unfold gluedIso
  rw [glueIso_hom_app_of_leU _ _ _ _ _ _ _ _ W le_top v]
  exact (Cover.mapSection_of_le (dual M) (form M 2) ⊤ D cover.ge (fun i => asPatch (s i))
    (compatible M ω D s hs) W le_top i hW v).trans (hs i W hW v)

include cover hs in
theorem gluedIso_apply (W : X.Opens) (v : (dual M).val.obj (op W)) :
    (gluedIso M ω D cover s hs).hom.val.app (op W) v =
      contractSection M W v ((form M 3).val.map (homOfLE (le_top : W ≤ ⊤)).op ω) := by
  let F := addSheaf (form M 2)
  apply F.eq_of_locally_eq' (fun i => W ⊓ D i) W (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, cover]; exact le_inf le_rfl le_top)
  intro i
  let g := (gluedIso M ω D cover s hs).hom.val
  let v' := (dual M).val.map (homOfLE (show W ⊓ D i ≤ W from inf_le_left)).op v
  let a := homOfLE (show W ⊓ D i ≤ W from inf_le_left)
  change (form M 2).val.map a.op (g.app (op W) v) =
    (form M 2).val.map a.op
      (contractSection M W v ((form M 3).val.map (homOfLE (le_top : W ≤ ⊤)).op ω))
  rw [← PresheafOfModules.naturality_apply g a.op v,
    contractSection_restrict M W v inf_le_left, ← PresheafOfModules.map_comp_apply]
  exact gluedIso_patch M ω D cover s hs i (W ⊓ D i) inf_le_right v'

end CycleQ2HodgeVolumeContraction
end

#print axioms CycleQ2HodgeVolumeContraction.gluedIso_apply
