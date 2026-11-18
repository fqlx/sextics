import Proposal.GeometricLocalHomTargetFrame
import Proposal.GeometricLiteralOrbitCurveNormal
import Proposal.GeometricLiteralCurvePositiveTwist

/-!
# The seventh twist of the dual conormal on each orbit component

Changing the target of a conormal functional from O_C to O_C(7)
multiplies its transition by the seventh power of the original
coordinate ratio. Each actual translated normal has the inverse-square
transition. Their product gives O_C(5).

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralTwistedConormalDual
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricModuleLocalIso CycleQ2GeometricCanonicalGluing CycleQ2SourceNormalSheaf
  CycleQ2LiteralCurvePositiveTwist CycleQ2LiteralOrbitCurveNormal CycleQ2LiteralOrbitAction
  CycleQ2LocalHomTargetFrame

private abbrev C := projectiveCurve 57 1
private abbrev U := firstProjectivePatch 57 1
private abbrev V := secondProjectivePatch 57 1
private abbrev W := overlapProjectivePatch 57 1
private abbrev hW := overlapProjectivePatch_eq 57 1
private abbrev τ := projectiveTransitionUnit 57 1
private abbrev j (z : ℂ) (hz : z ^ 3 = 1) := CycleQ2GeometricLiteralSurface.curveToSurface 57 1 ≫ (closedProjectiveAction z hz).inv

abbrev twistedNormal (z : ℂ) (hz : z ^ 3 = 1) :=
  moduleHomSheaf C.sheaf (sourceConormal (j z hz)) (curveTwistModule 7)

private def patchComp {A B D : C.Modules} {T : C.Opens}
    (e : PatchIso A B T) (g : PatchIso B D T) : PatchIso A D T where
  app O hO := (e.app O hO).trans (g.app O hO)
  naturality h hO s := by
    change D.val.map _ (g.app _ hO (e.app _ hO s)) = _
    rw [g.naturality, e.naturality]
    rfl

private def globalFrame {A B : C.Modules} (e : A ≅ B) (T : C.Opens) : PatchIso A B T where
  app O _ := ((SheafOfModules.evaluation C.ringCatSheaf (op O)).mapIso e).toLinearEquiv
  naturality h _ s := (ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality (homOfLE h).op) s).symm

private abbrev sevenU := twistedFirstFrame C.sheaf U V W hW (τ ^ 7)
private abbrev sevenV := twistedSecondFrame C.sheaf U V W hW (τ ^ 7)
private abbrev negTwoU := twistedFirstFrame C.sheaf U V W hW (normalTransitionUnit 57 1)
private abbrev negTwoV := twistedSecondFrame C.sheaf U V W hW (normalTransitionUnit 57 1)

private def first (z : ℂ) (hz : z ^ 3 = 1) : LocalFrame C.sheaf (twistedNormal z hz) U :=
  patchComp (postFrame (sourceConormal (j z hz)) sevenU)
    (patchComp (globalFrame (componentNormalModel z hz) U) negTwoU)

private def second (z : ℂ) (hz : z ^ 3 = 1) : LocalFrame C.sheaf (twistedNormal z hz) V :=
  patchComp (postFrame (sourceConormal (j z hz)) sevenV)
    (patchComp (globalFrame (componentNormalModel z hz) V) negTwoV)

private abbrev atFrame {T O : C.Opens} {M : C.Modules} (e : LocalFrame C.sheaf M T) (h : O ≤ T) :
    Γ(M,O) ≃ₗ[Γ(C,O)] Γ(C,O) := e.app O h

private abbrev uW : W ≤ U := hW.le.trans inf_le_left
private abbrev vW : W ≤ V := hW.le.trans inf_le_right

private theorem seven_change (z : ℂ) (hz : z ^ 3 = 1) (s : (twistedNormal z hz).val.obj (op W)) :
    (postFrame (sourceConormal (j z hz)) sevenU).app W uW s =
      (↑(τ ^ 7) : Γ(C,W)) • (postFrame (sourceConormal (j z hz)) sevenV).app W vW s := by
  apply localLinearHom_ext
  intro P m
  change atFrame sevenU (P.hom.le.trans uW) (s.val.app (op P) m) =
    C.presheaf.map P.hom.op (↑(τ ^ 7) : Γ(C,W)) * atFrame sevenV (P.hom.le.trans vW) (s.val.app (op P) m)
  exact TwistedModule.linearFrame_transition C.sheaf U V W hW (τ ^ 7) P.left P.hom.le (s.val.app (op P) m)

private theorem five_change (z : ℂ) (hz : z ^ 3 = 1) (s : (twistedNormal z hz).val.obj (op W)) :
    atFrame (first z hz) uW s = (↑(τ ^ 5) : Γ(C,W)) * atFrame (second z hz) vW s := by
  let n := ((componentNormalModel z hz).hom.app W) ((postFrame (sourceConormal (j z hz)) sevenV).app W vW s)
  change atFrame negTwoU uW (((componentNormalModel z hz).hom.app W) ((postFrame _ sevenU).app W uW s)) = _
  rw [seven_change, Scheme.Modules.Hom.app_smul, map_smul]
  have hn := TwistedModule.linearFrame_transition C.sheaf U V W hW (normalTransitionUnit 57 1) W le_rfl n
  rw [Twisted.res_self] at hn
  change atFrame negTwoU uW n = (normalTransitionUnit 57 1 : Γ(C,W)) * atFrame negTwoV vW n at hn
  change (↑(τ ^ 7) : Γ(C,W)) * atFrame negTwoU uW n = (↑(τ ^ 5) : Γ(C,W)) * atFrame negTwoV vW n
  rw [hn, ← mul_assoc]
  congr 1
  change (↑(τ ^ 7 * (τ⁻¹ ^ 2)) : Γ(C,W)) = ↑(τ ^ 5)
  congr 1
  group

/-- The actual twisted intrinsic conormal dual is the positive fifth twist. -/
def twistedNormalIso (z : ℂ) (hz : z ^ 3 = 1) : twistedNormal z hz ≅ curveTwistModule 5 := by
  apply canonicalIsoOfOverlap C.sheaf U V W hW (τ ^ 5) (twistedNormal z hz) (first z hz) (second z hz)
    (projective_twoOpen_cover 57 1 (by norm_num))
  let e := atFrame (first z hz) uW
  let f := atFrame (second z hz) vW
  apply e.injective
  change atFrame (first z hz) uW ((atFrame (second z hz) vW).symm 1) =
    atFrame (first z hz) uW ((↑(τ ^ 5) : Γ(C,W)) • (atFrame (first z hz) uW).symm 1)
  rw [map_smul, LinearEquiv.apply_symm_apply]
  exact (five_change z hz _).trans (congrArg (fun a : Γ(C,W) => (↑(τ ^ 5) : Γ(C,W)) * a)
    ((atFrame (second z hz) vW).apply_symm_apply (1 : Γ(C,W))))

end CycleQ2LiteralTwistedConormalDual
end

#print axioms CycleQ2LiteralTwistedConormalDual.twistedNormalIso
