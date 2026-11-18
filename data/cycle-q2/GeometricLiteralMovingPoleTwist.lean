import Proposal.GeometricLiteralCoordinateTwist
import Proposal.GeometricLiteralMovingDivisorOrbitFrames
import Proposal.GeometricLiteralMovingResiduePole
import Proposal.GeometricLiteralMovingResidueBasis
import Proposal.GeometricSurfaceCoordinateCubicFrames

/-!
# The seventh twist in the moving canonical pole sheaf

On each framed open, a section of O_D(7) gives a pole numerator by
multiplication by the local equation of the original orbit divisor.
The cubic change of canonical frames and the fourth twist of the moving
divisor give the seventh power in the chart change. The image is locally
the original orbit equation times the regular pole numerators.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingPoleTwist
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionSheafGlobal
  CycleQ2LiteralMovingDivisorOrbitFrames CycleQ2LiteralMovingIdealExact
  CycleQ2LiteralMovingResiduePole CycleQ2LiteralMovingResidueBasis
open CycleQ2SurfaceCoordinateFrames (coordinateExteriorFrame)
open CycleQ2SurfaceCoordinateCubicFrames (orientation orientation_mul_self coordinateExteriorFrame_transition)
open CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafLocal
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open CycleQ2GeometricModuleLocalIso (addSheaf)

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) {W : Surface.Opens}

private abbrev cframe (j : FrameData W) :
    CanonicalForms.val.obj (op W) ≃ₗ[Γ(Surface,W)] Γ(Surface,W) :=
  (coordinateExteriorFrame j.chart).app W j.within

private abbrev coeff (j : FrameData W) :
    Γ(ambientTwist 7,W) →ₗ[Γ(Surface,W)] Γ(Surface,W) := coordinate 7 j.chart W j.within

def numerator (j : FrameData W) (s : Γ(ambientTwist 7,W)) : CanonicalForms.val.obj (op W) :=
  (cframe j).symm ((orientation j.chart : Γ(Surface,W)) * pivotEquation j * coeff j s)

private theorem transition_power (u : Γ(Surface,W)ˣ) :
    ((u ^ (-(7 : ℤ)) : Γ(Surface,W)ˣ) : Γ(Surface,W)) =
      (↑u⁻¹ : Γ(Surface,W)) ^ 7 := by
  norm_num [zpow_neg, inv_pow]

theorem numerator_change (j l : FrameData W) (s : Γ(ambientTwist 7,W)) :
    (divisorTransition j l : Γ(Surface,W)) • numerator j s = numerator l s := by
  apply (cframe j).injective
  rw [map_smul, smul_eq_mul, numerator, LinearEquiv.apply_symm_apply]
  have he := coordinateExteriorFrame_transition j.chart l.chart W j.within l.within (numerator l s)
  change (cframe j) (numerator l s) = ((orientation j.chart : Γ(Surface,W)) * orientation l.chart) *
    (↑(transitionUnit j.chart l.chart W j.within l.within)⁻¹ : Γ(Surface,W)) ^ 3 *
    (cframe l) (numerator l s) at he
  rw [he, numerator, LinearEquiv.apply_symm_apply]
  let u := transitionUnit j.chart l.chart W j.within l.within
  have hs : coeff j s = (↑u⁻¹ : Γ(Surface,W)) ^ 7 * coeff l s := by
    rw [coordinate_transition 7 j.chart l.chart W j.within l.within s]
    exact congrArg (fun a : Γ(Surface,W) => a * coeff l s) (transition_power u)
  have hg : pivotEquation l = (orbitTransition j l : Γ(Surface,W)) * pivotEquation j :=
    orbitTransition_generator j l
  rw [hs, hg, divisorTransition_eq_twist_mul_orbit]
  change ((u : Γ(Surface,W)) ^ 4 * (orbitTransition j l : Γ(Surface,W))) * _ = _
  have hu : (u : Γ(Surface,W)) ^ 4 * (↑u⁻¹ : Γ(Surface,W)) ^ 7 =
      (↑u⁻¹ : Γ(Surface,W)) ^ 3 := by
    calc
      _ = ((u : Γ(Surface,W)) * (↑u⁻¹ : Γ(Surface,W))) ^ 4 * (↑u⁻¹ : Γ(Surface,W)) ^ 3 := by ring
      _ = _ := by rw [Units.mul_inv, one_pow, one_mul]
  have ho := orientation_mul_self l.chart W
  linear_combination (orbitTransition j l : Γ(Surface,W)) * (orientation j.chart : Γ(Surface,W)) *
    pivotEquation j * coeff l s * hu - (orientation j.chart : Γ(Surface,W)) * (↑u⁻¹ : Γ(Surface,W)) ^ 3 *
    (orbitTransition j l : Γ(Surface,W)) * pivotEquation j * coeff l s * ho

theorem numerator_restrict (j : FrameData W) (s : Γ(ambientTwist 7,W)) {V : Surface.Opens} (h : V ≤ W) :
    CanonicalForms.val.map (homOfLE h).op (numerator j s) =
      numerator (j.restrict h) (moduleRes (X := Surface) (ambientTwist 7) h s) := by
  apply (cframe (j.restrict h)).injective
  have he := (coordinateExteriorFrame j.chart).naturality h j.within (numerator j s)
  change (targetRes h) ((cframe j) (numerator j s)) =
    (cframe (j.restrict h)) (CanonicalForms.val.map (homOfLE h).op (numerator j s)) at he
  rw [← he, numerator, numerator, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    map_mul, map_mul, map_intCast, pivotEquation_restrict]
  exact congrArg (fun a : Γ(Surface,V) => (orientation j.chart : Γ(Surface,V)) * pivotEquation (j.restrict h) * a)
    (CycleQ2LiteralMovingIdealExact.coordinate_restrict 7 j.chart h j.within s)

def localInclusion (j : FrameData W) :
    Γ(ambientTwist 7,W) →+ (PoleForms t).val.obj (op W) :=
  (poleMap t ht j).comp ((cframe j).symm.toAddEquiv.toAddMonoidHom.comp
    ((AddMonoidHom.mulLeft ((orientation j.chart : Γ(Surface,W)) * pivotEquation j)).comp
      (coeff j).toAddMonoidHom))

theorem localInclusion_change (j l : FrameData W) (s : Γ(ambientTwist 7,W)) :
    localInclusion t ht j s = localInclusion t ht l s := by
  change poleOfNumerator t ht j (numerator j s) = poleOfNumerator t ht l (numerator l s)
  rw [pole_change_frame t ht j l, numerator_change]

theorem localInclusion_restrict (j : FrameData W) (s : Γ(ambientTwist 7,W)) {V : Surface.Opens} (h : V ≤ W) :
    (PoleForms t).val.map (homOfLE h).op (localInclusion t ht j s) =
      localInclusion t ht (j.restrict h) (moduleRes (X := Surface) (ambientTwist 7) h s) := by
  change (PoleForms t).val.map _ (poleOfNumerator t ht j (numerator j s)) = _
  rw [poleOfNumerator_restrict, numerator_restrict]
  rfl

/-- The morphism O_D(7) → K_D(Γ) on the full surface. -/
def twistInclusion : addSheaf (ambientTwist 7) ⟶ addSheaf (PoleForms t) :=
  extend (fun W => localInclusion t ht W.frame) (by
    intro W V h s
    exact ((localInclusion_restrict t ht W.frame s h).trans
      (localInclusion_change t ht (W.frame.restrict h) V.frame _)).symm)

end CycleQ2LiteralMovingPoleTwist
end

#print axioms CycleQ2LiteralMovingPoleTwist.twistInclusion
