import Proposal.GeometricLiteralMovingPoleComponentsImmersion
import Proposal.GeometricNormalSheafComparison
import Proposal.GeometricSeedSectionBalance
import Proposal.GeometricLiteralCurvePositiveTwist
import Proposal.GeometricLiteralCoordinateTwist

/-!
# Pullback of the coordinate transition along the three curve immersions

On the original two curve charts, the translated immersion pulls the surface
ratio X₂/X₁ back to z times the original transition unit. The formula holds
on every common subopen, with both the surface and the curve restrictions
taken by their scheme morphisms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralOrbitCurveTwistPullback

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace MvPolynomial
  CycleQ2CartierSurfaceGrading CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceOverlap
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SurfaceCoordinateSections
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricTwistedDifferential
  CycleQ2SeedProjectiveImageCocycle CycleQ2SurfaceOverlapSections
  CycleQ2LiteralOrbitAction CycleQ2LiteralMovingDivisorOrbitPullback
  CycleQ2NormalTransitionBinding CycleQ2LiteralMovingPoleComponents

private abbrev Curve := projectiveCurve 57 1

/-- Complex constants on the original projective curve. -/
abbrev curveScalar (W : Curve.Opens) : ℂ →+* Γ(Curve,W) :=
  coefficientOn Curve.sheaf (CycleQ2GeometricDifferentialSheaf.projectiveGlobalCoefficient 57 1) W

private abbrev surfaceScalar (V : Surface.Opens) : ℂ →+* Γ(Surface,V) :=
  coefficientOn Surface.sheaf (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1) V

private theorem polynomial_constant (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) (c : ℂ) :
    polynomialSection i V hi (C c) = surfaceScalar V c := by
  rw [← CycleQ2SeedSectionBalance.sectionConstant_entry]
  change CycleQ2GeometricAffineChartSections.chartSection _ _ (algebraMap ℂ _ c) = _
  rw [coordinate_chartSection_subopen,
    ← CycleQ2GeometricSurfaceCoefficients.coordinateSectionsEquiv_coefficient 57 1 i.succ c,
    RingEquiv.symm_apply_apply]
  exact coefficientOn_restrict _ _ hi c

private theorem first_ratio (V : Surface.Opens) (hV : V ≤ overlapPatch 57 1) :
    polynomialSection 0 V (hV.trans (overlap_le_first 57 1)) (X 2) =
      coordinateSection 57 1 V hV := by
  let hp : (X (2 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 := isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight 2
  change coordinatePolynomialSection 57 1 1 V _ (X 2) = _
  rw [← first_chart_polynomial_section 57 1 V _ 1 (X 2) hp,
    first_chartSection_subopen, coordinateSection_restrict_first]
  simp only [firstSurfaceDehomogenize, aeval_X, Matrix.cons_val_two]
  rfl

private theorem seed_constant (V : Surface.Opens) (W : Curve.Opens) (hW : W ≤ seedImmersion ⁻¹ᵁ V)
    (c : ℂ) : seedImmersion.appLE V W hW (surfaceScalar V c) = curveScalar W c := by
  change Curve.presheaf.map (homOfLE hW).op (seedImmersion.app V (surfaceScalar V c)) = _
  exact (congrArg (Curve.presheaf.map (homOfLE hW).op)
    (CycleQ2GeometricSurfaceComplexRestriction.curveToSurface_coefficient_app 57 1 V c)).trans
      (coefficientOn_restrict _ _ hW c)

private theorem action_ratio (z : ℂ) (hz : z^3 = 1) (V P : Surface.Opens)
    (hV : V ≤ Patch 0) (hP : P ≤ (closedProjectiveAction z hz).hom ⁻¹ᵁ V)
    (hP₀ : P ≤ Patch 0) :
    (closedProjectiveAction z hz).hom.appLE V P hP (polynomialSection 0 V hV (X 2)) =
      surfaceScalar P z⁻¹ * polynomialSection 0 P hP₀ (X 2) := by
  let hp : (X (2 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 := isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight 2
  rw [polynomialSection_pullback z hz 0 V P hV hP 1 (X 2) hp]
  have h : C ((coordinateScale z 0)⁻¹ ^ 1) * CycleQ2SeedCyclicAction.polynomialAction z (X 2) =
      C z⁻¹ * (X (2 : Fin 5) : MvPolynomial (Fin 5) ℂ) := by
    rw [CycleQ2SeedCyclicAction.polynomialAction_X]
    change C ((z^2)⁻¹ ^ 1) * (C z * X 2) = _
    rw [pow_one, ← mul_assoc, ← map_mul]
    have hn : z ≠ 0 := by rintro rfl; norm_num at hz
    congr 2
    field_simp
  rw [h, map_mul, polynomial_constant]

private theorem pulled_ratio (w : ℂ) (hw : w^3 = 1) (V : Surface.Opens)
    (hV : V ≤ overlapPatch 57 1) (W : Curve.Opens) (hW : W ≤ overlapProjectivePatch 57 1)
    (hWV : W ≤ (seedImmersion ≫ (closedProjectiveAction w hw).hom) ⁻¹ᵁ V) :
    (seedImmersion ≫ (closedProjectiveAction w hw).hom).appLE V W hWV
        (polynomialSection 0 V (hV.trans (overlap_le_first 57 1)) (X 2)) =
      curveScalar W w⁻¹ * curveRestriction 57 1 W hW
        (projectiveTransitionUnit 57 1 : Γ(Curve,overlapProjectivePatch 57 1)) := by
  let f := (closedProjectiveAction w hw).hom
  let P := f ⁻¹ᵁ V
  have h₀ : P ≤ Patch 0 := (f.preimage_mono (hV.trans (overlap_le_first 57 1))).trans (preimage_patch_le w hw 0)
  have h₁ : P ≤ Patch 1 := (f.preimage_mono (hV.trans (overlap_le_second 57 1))).trans (preimage_patch_le w hw 1)
  have hP : P ≤ overlapPatch 57 1 := by rw [overlapPatch_eq]; exact le_inf h₀ h₁
  let y := polynomialSection 0 V (hV.trans (overlap_le_first 57 1)) (X 2)
  have hcomp := ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE seedImmersion f V P W le_rfl hWV) y
  refine hcomp.symm.trans ?_
  change seedImmersion.appLE P W hWV (f.appLE V P le_rfl y) = _
  rw [show f.appLE V P le_rfl y = surfaceScalar P w⁻¹ * polynomialSection 0 P h₀ (X 2) from
    action_ratio w hw V P _ le_rfl h₀, map_mul, seed_constant, first_ratio P hP]
  exact congrArg (curveScalar W w⁻¹ * ·) (coordinateSection_pullback 57 1 P hP W hW hWV)

private theorem inverse_action (z : ℂ) (hz : z^3 = 1) (hi : z⁻¹^3 = 1) :
    (closedProjectiveAction z hz).inv = (closedProjectiveAction z⁻¹ hi).hom := by
  apply (cancel_epi (closedProjectiveAction z hz).hom).mp
  rw [Iso.hom_inv_id, closedProjectiveAction_hom_comp]
  have hn : z ≠ 0 := by rintro rfl; norm_num at hz
  simpa only [mul_inv_cancel₀ hn] using closedProjectiveAction_hom_one.symm

/-- Each original curve coordinate chart is the preimage of its surface chart. -/
theorem component_preimage_patch (z : ℂ) (hz : z^3 = 1) (i : Fin 3) :
    (componentImmersion z hz) ⁻¹ᵁ Patch i = coordinateProjectivePatch 57 1 i.succ := by
  have hi : z⁻¹ ^ 3 = 1 := by rw [inv_pow, hz, inv_one]
  rw [componentImmersion, inverse_action z hz hi, Scheme.Hom.comp_preimage, preimage_patch]
  exact CycleQ2GeometricSurfaceCurveCharts.coordinateCurvePreimage 57 1 i.succ

theorem quarticOverlap_le_component_preimage (z : ℂ) (hz : z^3 = 1) :
    overlapProjectivePatch 57 1 ≤ (componentImmersion z hz) ⁻¹ᵁ (Patch 0 ⊓ Patch 1) := by
  change overlapProjectivePatch 57 1 ≤ (componentImmersion z hz) ⁻¹ᵁ Patch 0 ⊓
    (componentImmersion z hz) ⁻¹ᵁ Patch 1
  rw [component_preimage_patch, component_preimage_patch, overlapProjectivePatch_eq]
  exact inf_le_inf (CycleQ2GeometricProjectiveAffine.firstProjectivePatch_le_firstCoordinate 57 1)
    (CycleQ2GeometricProjectiveAffine.secondProjectivePatch_le_secondCoordinate 57 1)

/-- The actual first curve frame is related to the second by the original
quartic-overlap ratio, multiplied by the character of the inverse action. -/
theorem component_ratio (z : ℂ) (hz : z^3 = 1) (V : Surface.Opens)
    (h₀ : V ≤ Patch 0) (h₁ : V ≤ Patch 1) (W : Curve.Opens)
    (hW : W ≤ overlapProjectivePatch 57 1) (hWV : W ≤ (componentImmersion z hz) ⁻¹ᵁ V) :
    (componentImmersion z hz).appLE V W hWV (transitionUnit 1 0 V h₁ h₀ : Γ(Surface,V)) =
      curveScalar W z * curveRestriction 57 1 W hW
        (projectiveTransitionUnit 57 1 : Γ(Curve,overlapProjectivePatch 57 1)) := by
  have hV : V ≤ overlapPatch 57 1 := by rw [overlapPatch_eq]; exact le_inf h₀ h₁
  have hi : z⁻¹ ^ 3 = 1 := by rw [inv_pow, hz, inv_one]
  have hj : componentImmersion z hz = seedImmersion ≫ (closedProjectiveAction z⁻¹ hi).hom :=
    congrArg (seedImmersion ≫ ·) (inverse_action z hz hi)
  revert hWV
  rw [hj]
  intro hWV
  rw [show (transitionUnit 1 0 V h₁ h₀ : Γ(Surface,V)) = polynomialSection 0 V h₀ (X 2) from rfl]
  simpa only [inv_inv] using pulled_ratio z⁻¹ hi V hV W hW hWV

/-- Pullback of the degree-seven transition in the actual pole coordinate. -/
theorem component_seventh (z : ℂ) (hz : z^3 = 1) (V : Surface.Opens)
    (h₀ : V ≤ Patch 0) (h₁ : V ≤ Patch 1) (W : Curve.Opens)
    (hW : W ≤ overlapProjectivePatch 57 1) (hWV : W ≤ (componentImmersion z hz) ⁻¹ᵁ V) :
    (componentImmersion z hz).appLE V W hWV ((transitionUnit 1 0 V h₁ h₀ : Γ(Surface,V))^7) =
      curveScalar W z * curveRestriction 57 1 W hW
        ((projectiveTransitionUnit 57 1 : Γ(Curve,overlapProjectivePatch 57 1))^7) := by
  have h7 : z^7 = z := by calc
    z^7 = (z^3)^2 * z := by ring
    _ = z := by rw [hz, one_pow, one_mul]
  rw [map_pow, component_ratio, mul_pow, ← map_pow, h7, map_pow]

/-- The original entire quartic overlap lies inside the translated surface
coordinate overlap, so the seventh-power formula applies there. -/
theorem component_overlap_seventh (z : ℂ) (hz : z^3 = 1) :
    (componentImmersion z hz).appLE (Patch 0 ⊓ Patch 1) (overlapProjectivePatch 57 1)
      (quarticOverlap_le_component_preimage z hz)
      ((transitionUnit 1 0 _ inf_le_right inf_le_left : Γ(Surface,Patch 0 ⊓ Patch 1)) ^ 7) =
      curveScalar (overlapProjectivePatch 57 1) z *
        (projectiveTransitionUnit 57 1 : Γ(Curve,overlapProjectivePatch 57 1)) ^ 7 := by
  have h := component_seventh z hz _ inf_le_left inf_le_right _ le_rfl
    (quarticOverlap_le_component_preimage z hz)
  simpa [curveRestriction] using h

open CycleQ2LiteralMovingIdealExact (ambientTwist coordinate scalarUnit coordinate_transition)
open CycleQ2LiteralCurvePositiveTwist (curveTwistModule firstTwistFrame secondTwistFrame)

/-- Pulling back coordinates of an actual O_D(7) section gives the original
curve gluing relation after multiplication by z in the second frame. -/
theorem component_coordinate (z : ℂ) (hz : z^3 = 1) (V : Surface.Opens)
    (h₀ : V ≤ Patch 0) (h₁ : V ≤ Patch 1) (W : Curve.Opens)
    (hW : W ≤ overlapProjectivePatch 57 1) (hWV : W ≤ (componentImmersion z hz) ⁻¹ᵁ V)
    (x : Γ(ambientTwist 7,V)) :
    (componentImmersion z hz).appLE V W hWV (coordinate 7 0 V h₀ x) =
      curveRestriction 57 1 W hW ((projectiveTransitionUnit 57 1 : Γ(Curve,overlapProjectivePatch 57 1) )^7) *
        (curveScalar W z * (componentImmersion z hz).appLE V W hWV (coordinate 7 1 V h₁ x)) := by
  have h : scalarUnit 7 0 1 V h₀ h₁ = transitionUnit 1 0 V h₁ h₀ ^ (7 : ℕ) := by
    rw [scalarUnit, transitionUnit_symm 0 1]
    simp
  rw [coordinate_transition 7 0 1 V h₀ h₁ x, h, Units.val_pow_eq_pow_val,
    map_mul, component_seventh z hz V h₀ h₁ W hW hWV]
  ring

/-- The pulled chart coordinates determine a unique actual O_C(7) section
on each common subopen of the original quartic cover. -/
theorem existsUnique_curveTwistSection (z : ℂ) (hz : z^3 = 1) (V : Surface.Opens)
    (h₀ : V ≤ Patch 0) (h₁ : V ≤ Patch 1) (W : Curve.Opens)
    (hW : W ≤ overlapProjectivePatch 57 1) (hWV : W ≤ (componentImmersion z hz) ⁻¹ᵁ V)
    (x : Γ(ambientTwist 7,V)) :
    ∃! y : (curveTwistModule 7).val.obj (op W),
      (firstTwistFrame 7).app W (hW.trans ((overlapProjectivePatch_eq 57 1).le.trans inf_le_left)) y =
        (componentImmersion z hz).appLE V W hWV (coordinate 7 0 V h₀ x) ∧
      (secondTwistFrame 7).app W (hW.trans ((overlapProjectivePatch_eq 57 1).le.trans inf_le_right)) y =
        curveScalar W z * (componentImmersion z hz).appLE V W hWV (coordinate 7 1 V h₁ x) := by
  let q := curveScalar W z * (componentImmersion z hz).appLE V W hWV (coordinate 7 1 V h₁ x)
  let e := (secondTwistFrame 7).app W (hW.trans ((overlapProjectivePatch_eq 57 1).le.trans inf_le_right))
  let y := e.symm q
  have hy : e y = q := e.apply_symm_apply q
  refine ⟨y, ⟨?_, hy⟩, fun y' hy' => e.injective (hy'.2.trans hy.symm)⟩
  have h := Twisted.localSections_transition Curve.sheaf _ _ _ (overlapProjectivePatch_eq 57 1)
    (projectiveTransitionUnit 57 1 ^ 7) W hW y
  change _ = curveRestriction 57 1 W hW ((projectiveTransitionUnit 57 1 : Γ(Curve,overlapProjectivePatch 57 1))^7) * (show Γ(Curve,W) from e y) at h
  rw [hy] at h
  exact h.trans (component_coordinate z hz V h₀ h₁ W hW hWV x).symm

end CycleQ2LiteralOrbitCurveTwistPullback
end

#print axioms CycleQ2LiteralOrbitCurveTwistPullback.component_ratio
#print axioms CycleQ2LiteralOrbitCurveTwistPullback.component_seventh

#print axioms CycleQ2LiteralOrbitCurveTwistPullback.existsUnique_curveTwistSection
