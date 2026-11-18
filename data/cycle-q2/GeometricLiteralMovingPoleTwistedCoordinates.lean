import Proposal.GeometricLiteralMovingPoleNormalEvaluation
import Proposal.GeometricLiteralOrbitCurveTwistFrames

/-!
# Normal coefficients of the positive pole quotient

On every framed neighborhood meeting one orbit component, evaluation of the
twisted conormal functional followed by the pulled seventh-twist frame gives
a curve-ring coefficient. Its change of coordinates is the same product of
the seventh power and the pivot transition as for the actual pole quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingPoleNormalEvaluation

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralMovingPoleComponents CycleQ2LiteralMovingResidueBasis CycleQ2SeedProjectiveImageCocycle
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricDifferentialSheaf CycleQ2GeometricModuleLocalIso CycleQ2LiteralCurvePositiveTwist
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralOrbitChern CycleQ2LiteralOrbitCurveTwistFrames
  CycleQ2SeedSectionDivisorTransitions CycleQ2LinkageComponentAlgebra CycleQ2LinkageComponentDecomposition

private abbrev C := projectiveCurve 57 1
private abbrev j := curveComponent
private theorem hcube (a : Fin 3) : z a ^ 3 = 1 := rootValues_cube complexRoot complexRoot_quadratic a

private abbrev seven (a : Fin 3) (i : Fin 3) (O : C.Opens) (h : O ≤ j a ⁻¹ᵁ Patch i) :
    Γ(curveTwistModule 7,O) ≃ₗ[Γ(C,O)] Γ(C,O) := (componentFrame (z a) (hcube a) i).app O h

/-- The coefficient of an actual O(7)-valued conormal functional on each surviving component. -/
def coefficient (a : Fin 3) (W : FramedAffine) (w : Fin 3 → Vertex)
    (hw : WithinTranslatedCover W w) (ho : AvoidsOtherComponents W a) (O : Surface.Opens) (h : O ≤ W.carrier) :
    Γ(pushedNormal a,O) ≃+ Γ(C,j a ⁻¹ᵁ O) :=
  ((evaluation a W w hw ho).app O h).toAddEquiv.trans
    (seven a W.frame.chart _ ((j a).preimage_mono (h.trans W.frame.within))).toAddEquiv

private theorem coeff_restrict (a : Fin 3) (W : FramedAffine) (w : Fin 3 → Vertex)
    (hw : WithinTranslatedCover W w) (ho : AvoidsOtherComponents W a) (V : Surface.Opens) (h : V ≤ W.carrier)
    (s : Γ(pushedNormal a,W.carrier)) :
    C.presheaf.map (homOfLE ((j a).preimage_mono h)).op (coefficient a W w hw ho _ le_rfl s) =
      coefficient a W w hw ho V h ((pushedNormal a).val.map (homOfLE h).op s) := by
  change C.presheaf.map _ (seven _ _ _ _ _) = _
  rw [(componentFrame (z a) (hcube a) W.frame.chart).naturality]
  exact congrArg (seven a W.frame.chart _ _) ((evaluation a W w hw ho).naturality h le_rfl s)

theorem coefficient_restrict_change (a : Fin 3) (W V : FramedAffine) (w v : Fin 3 → Vertex)
    (hw : WithinTranslatedCover W w) (hv : WithinTranslatedCover V v)
    (hwo : AvoidsOtherComponents W a) (hvo : AvoidsOtherComponents V a)
    (h : V.carrier ≤ W.carrier) (s : Γ(pushedNormal a,W.carrier)) :
    coefficient a V v hv hvo _ le_rfl ((pushedNormal a).val.map (homOfLE h).op s) =
      (j a).app V.carrier (((transitionUnit W.frame.chart V.frame.chart V.carrier
        (h.trans W.frame.within) V.frame.within : Γ(Surface,V.carrier)) ^ 7) *
          (orbitTransition (W.frame.restrict h) V.frame : Γ(Surface,V.carrier))) *
        C.presheaf.map (homOfLE ((j a).preimage_mono h)).op (coefficient a W w hw hwo _ le_rfl s) := by
  rw [coeff_restrict]
  let O := V.carrier
  let g : Γ(Surface,O) := orbitTransition (W.frame.restrict h) V.frame
  let s' := (pushedNormal a).val.map (homOfLE h).op s
  let m : Γ(curveTwistModule 7, j a ⁻¹ᵁ O) := (evaluation a W w hw hwo).app O h s'
  have he := evaluation_change a W V w v hw hv hwo hvo O h le_rfl s'
  change (evaluation a V v hv hvo).app O le_rfl s' = (j a).app O g • m at he
  change seven a V.frame.chart _ _ ((evaluation a V v hv hvo).app O le_rfl s') = _ * seven a W.frame.chart _ _ m
  rw [he, map_smul]
  have hc := componentFrame_change (z a) (hcube a) W.frame.chart V.frame.chart (j a ⁻¹ᵁ O)
    ((j a).preimage_mono (h.trans W.frame.within)) ((j a).preimage_mono V.frame.within) m
  rw [← pulledUnit_on (z a) (hcube a) W.frame.chart V.frame.chart O (j a ⁻¹ᵁ O)
    (h.trans W.frame.within) V.frame.within le_rfl] at hc
  change seven a V.frame.chart _ _ m = ((j a).app O _) ^ 7 * seven a W.frame.chart _ _ m at hc
  rw [hc, map_mul, map_pow]
  change (j a).app O g * (_ * _) = (_ * (j a).app O g) * _
  ring

end CycleQ2LiteralMovingPoleNormalEvaluation
end

#print axioms CycleQ2LiteralMovingPoleNormalEvaluation.coefficient_restrict_change
