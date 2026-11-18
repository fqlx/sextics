import Proposal.GeometricLiteralMovingPoleComponentsImmersionFrames
import Proposal.GeometricLocalHomSourceFrame
import Proposal.GeometricLiteralTwistedConormalDual

/-!
# Evaluating the twisted normal functional on each isolated component

The internal-Hom adjunction realizes a section on the translated curve as
a functional on its actual surface ideal. Evaluation at the orbit pivot
is an isomorphism on the whole framed neighborhood. The resulting sections
of the positive seventh twist acquire precisely the component of the orbit
transition when the pivot changes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingPoleNormalEvaluation

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2LiteralMovingPoleComponents CycleQ2LiteralMovingResidueBasis CycleQ2SeedProjectiveImageCocycle
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricDifferentialSheaf CycleQ2GeometricModuleLocalIso CycleQ2GeometricIntrinsicNormal
  CycleQ2SourceNormalSheaf CycleQ2NormalPushforwardIso CycleQ2LiteralTwistedConormalDual
  CycleQ2LiteralCurvePositiveTwist CycleQ2LiteralProjectiveIntersections CycleQ2LiteralOrbitChern
  CycleQ2SeedSectionDivisorTransitions

abbrev z (a : Fin 3) := rootValues complexRoot a
private theorem cube (a : Fin 3) : z a ^ 3 = 1 := rootValues_cube complexRoot complexRoot_quadratic a

abbrev normal (a : Fin 3) := twistedNormal (z a) (cube a)
abbrev pushedNormal (a : Fin 3) := (Scheme.Modules.pushforward (curveComponent a)).obj (normal a)
abbrev pushedSeven (a : Fin 3) := (Scheme.Modules.pushforward (curveComponent a)).obj (curveTwistModule 7)

private def adj (a : Fin 3) : pushedNormal a ≅
    moduleHomSheaf Surface.sheaf (idealModule (curveComponent a)) (pushedSeven a) :=
  internalHomPushforwardIso (curveComponent a) (idealModule _) (curveTwistModule 7)

/-- The original twist-valued functional evaluated on the actual local ideal generator. -/
def evaluation (a : Fin 3) (W : FramedAffine) (v : Fin 3 → Vertex) (hv : WithinTranslatedCover W v)
    (hoff : AvoidsOtherComponents W a) : PatchIso (pushedNormal a) (pushedSeven a) W.carrier where
  app O h :=
    (((SheafOfModules.evaluation Surface.ringCatSheaf (op O)).mapIso (adj a)).toLinearEquiv).trans
      ((CycleQ2LocalHomSourceFrame.frame (pushedSeven a) (componentKernelPatchIso a W v hv hoff)).app O h)
  naturality {O P} h hW s := by
    let e := CycleQ2LocalHomSourceFrame.frame (pushedSeven a) (componentKernelPatchIso a W v hv hoff)
    exact (e.naturality h hW ((adj a).hom.app O s)).trans
      (congrArg (e.app P (h.trans hW))
        ((ConcreteCategory.congr_hom ((adj a).hom.mapPresheaf.naturality (homOfLE h).op) s).symm))

theorem evaluation_change (a : Fin 3) (W V : FramedAffine) (w v : Fin 3 → Vertex)
    (hw : WithinTranslatedCover W w) (hv : WithinTranslatedCover V v)
    (hwo : AvoidsOtherComponents W a) (hvo : AvoidsOtherComponents V a)
    (O : Surface.Opens) (hW : O ≤ W.carrier) (hV : O ≤ V.carrier) (s : Γ(pushedNormal a,O)) :
    (evaluation a V v hv hvo).app O hV s =
      (orbitTransition (W.frame.restrict hW) (V.frame.restrict hV) : Γ(Surface,O)) •
        (evaluation a W w hw hwo).app O hW s := by
  let u : Γ(Surface,O) := orbitTransition (W.frame.restrict hW) (V.frame.restrict hV)
  have h := componentKernelPatchIso_change a W V w v hw hv hwo hvo O hW hV (1 : Γ(Surface,O))
  have he : (componentKernelPatchIso a V v hv hvo).app O hV (1 : Γ(Surface,O)) =
      u • (componentKernelPatchIso a W w hw hwo).app O hW (1 : Γ(Surface,O)) := by
    rw [← ((componentKernelPatchIso a W w hw hwo).app O hW).map_smul]
    simpa only [one_mul, Algebra.id.smul_eq_mul, mul_one] using h
  exact CycleQ2LocalHomSourceFrame.frame_change (pushedSeven a) (componentKernelPatchIso a W w hw hwo)
    (componentKernelPatchIso a V v hv hvo) hW hV u he ((adj a).hom.app O s)

end CycleQ2LiteralMovingPoleNormalEvaluation
end

#print axioms CycleQ2LiteralMovingPoleNormalEvaluation.evaluation_change
