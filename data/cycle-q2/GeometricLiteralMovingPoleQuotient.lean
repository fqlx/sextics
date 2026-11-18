import Proposal.GeometricLiteralMovingPoleTwist
import Proposal.GeometricLiteralMovingResidueAffineNumerators
import Proposal.GeometricLiteralTwistHOne

/-!
# The quotient of moving pole forms by the seventh twist

Locally the inclusion multiplies by the orbit equation. It is a
monomorphism, and on every framed affine open the sections of its
cokernel are the original section ring modulo the orbit equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingPoleQuotient
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionSheafGlobal
  CycleQ2LiteralMovingDivisorOrbitFrames CycleQ2LiteralMovingIdealExact CycleQ2LiteralMovingPoleTwist
  CycleQ2LiteralMovingResiduePole CycleQ2LiteralMovingResidueBasis
  CycleQ2GeometricProjectiveHOne CycleQ2CechTwoToDerived
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open CycleQ2SurfaceCoordinateFrames (coordinateExteriorFrame)
open CycleQ2SurfaceCoordinateCubicFrames (orientation orientation_mul_self)
open CycleQ2LiteralMovingResidueAffineNumerators (poleMap_surjective)
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : TopCat.{0}) : HasExt.{1} (X.Sheaf AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) {W : Surface.Opens}

private theorem recoverNumerator (j : FrameData W) (σ : CanonicalForms.val.obj (op W)) :
    (poleMap t ht j σ).val.app (op (Over.mk (𝟙 W))) (frame t ht (j.restrict le_rfl) 1) = σ := by
  change (poleOfNumerator t ht j σ).val.app _ _ = _
  exact (poleOfNumerator_app_frame t ht j σ (Over.mk (𝟙 W)) 1).trans
    ((one_smul Γ(Surface,W) (CanonicalForms.val.map (𝟙 (op W)) σ : CanonicalForms.val.obj (op W))).trans
      (ConcreteCategory.congr_hom (CanonicalForms.val.presheaf.map_id (op W)) σ))

def poleEquiv (j : FrameData W) : CanonicalForms.val.obj (op W) ≃+ (PoleForms t).val.obj (op W) :=
  AddEquiv.ofBijective (poleMap t ht j) ⟨by
    intro a b h
    rw [← recoverNumerator t ht j a, ← recoverNumerator t ht j b, h], poleMap_surjective t ht j⟩

private abbrev nativeFrame (j : FrameData W) :
    CanonicalForms.val.obj (op W) ≃ₗ[Γ(Surface,W)] Γ(Surface,W) :=
  (coordinateExteriorFrame j.chart).app W j.within

private def orient (i : Fin 3) (W : Surface.Opens) : Γ(Surface,W) ≃+ Γ(Surface,W) where
  toFun x := (orientation i : Γ(Surface,W)) * x
  invFun x := (orientation i : Γ(Surface,W)) * x
  left_inv x := by
    change (orientation i : Γ(Surface,W)) * ((orientation i : Γ(Surface,W)) * x) = x
    rw [← mul_assoc, orientation_mul_self, one_mul]
  right_inv x := by
    change (orientation i : Γ(Surface,W)) * ((orientation i : Γ(Surface,W)) * x) = x
    rw [← mul_assoc, orientation_mul_self, one_mul]
  map_add' _ _ := mul_add _ _ _

/-- The coefficient of a pole in the oriented canonical frame and the
original moving divisor frame. -/
def poleCoordinate (j : FrameData W) : (PoleForms t).val.obj (op W) ≃+ Γ(Surface,W) :=
  (poleEquiv t ht j).symm.trans ((nativeFrame j).toAddEquiv.trans
    (orient j.chart W))

theorem poleCoordinate_poleMap (j : FrameData W) (σ : CanonicalForms.val.obj (op W)) :
    poleCoordinate t ht j (poleMap t ht j σ) =
      (orientation j.chart : Γ(Surface,W)) * (nativeFrame j) σ := by
  change (orientation j.chart : Γ(Surface,W)) * ((nativeFrame j)
      ((poleEquiv t ht j).symm (poleEquiv t ht j σ))) = _
  rw [AddEquiv.symm_apply_apply]

/-- The change of pole coefficient is the seventh power of the coordinate
change multiplied by the transition of the orbit ideal. -/
theorem poleCoordinate_change (j l : FrameData W) (H : (PoleForms t).val.obj (op W)) :
    poleCoordinate t ht l H =
      ((transitionUnit j.chart l.chart W j.within l.within : Γ(Surface,W)) ^ 7 *
        (orbitTransition j l : Γ(Surface,W))) * poleCoordinate t ht j H := by
  obtain ⟨σ,rfl⟩ := poleMap_surjective t ht j H
  have hchange : poleMap t ht j σ =
      poleMap t ht l ((divisorTransition j l : Γ(Surface,W)) • σ) := pole_change_frame t ht j l σ
  rw [poleCoordinate_poleMap, hchange, poleCoordinate_poleMap, map_smul, smul_eq_mul]
  have he := CycleQ2SurfaceCoordinateCubicFrames.coordinateExteriorFrame_transition l.chart j.chart
    W l.within j.within σ
  change (nativeFrame l) σ =
    ((orientation l.chart : Γ(Surface,W)) * orientation j.chart) *
      (transitionUnit j.chart l.chart W j.within l.within : Γ(Surface,W)) ^ 3 *
      (nativeFrame j) σ at he
  rw [he, divisorTransition_eq_twist_mul_orbit]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  linear_combination (transitionUnit j.chart l.chart W j.within l.within : Γ(Surface,W)) ^ 7 *
    (orbitTransition j l : Γ(Surface,W)) * (orientation j.chart : Γ(Surface,W)) *
    (show Γ(Surface,W) from (nativeFrame j) σ) * orientation_mul_self l.chart W

theorem poleCoordinate_restrict (j : FrameData W) {V : Surface.Opens} (h : V ≤ W)
    (H : (PoleForms t).val.obj (op W)) :
    targetRes h (poleCoordinate t ht j H) =
      poleCoordinate t ht (j.restrict h) ((PoleForms t).val.map (homOfLE h).op H) := by
  obtain ⟨σ,rfl⟩ := poleMap_surjective t ht j H
  have hres : (PoleForms t).val.map (homOfLE h).op (poleMap t ht j σ) =
      poleMap t ht (j.restrict h) (CanonicalForms.val.map (homOfLE h).op σ) :=
    poleOfNumerator_restrict t ht j σ h
  rw [hres, poleCoordinate_poleMap, poleCoordinate_poleMap, map_mul, map_intCast]
  exact congrArg (fun a : Γ(Surface,V) => (orientation j.chart : Γ(Surface,V)) * a)
    ((coordinateExteriorFrame j.chart).naturality h j.within σ)

theorem poleCoordinate_localInclusion (j : FrameData W) (s : Γ(ambientTwist 7,W)) :
    poleCoordinate t ht j (localInclusion t ht j s) = pivotEquation j * coordinate 7 j.chart W j.within s := by
  change (orientation j.chart : Γ(Surface,W)) *
    ((nativeFrame j)
      ((poleEquiv t ht j).symm (poleEquiv t ht j (numerator j s)))) = _
  rw [AddEquiv.symm_apply_apply, numerator, LinearEquiv.apply_symm_apply]
  have h := orientation_mul_self j.chart W
  linear_combination pivotEquation j * coordinate 7 j.chart W j.within s * h

theorem inclusion_mono : Mono (twistInclusion t ht) := by
  constructor
  intro Z a b he
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ isBasis_framedAffine
  intro V
  apply ConcreteCategory.hom_ext
  intro x
  have h := congrArg (fun h : Z ⟶ addSheaf (PoleForms t) => h.hom.app (op V.carrier) x) he
  change (twistInclusion t ht).hom.app _ (a.hom.app _ x) = (twistInclusion t ht).hom.app _ (b.hom.app _ x) at h
  unfold twistInclusion at h
  rw [extend_apply, extend_apply] at h
  apply coordinate_injective 7 V.frame.chart V.carrier V.frame.within
  apply pivotEquation_regular V.frame
  have h' := congrArg (poleCoordinate t ht V.frame) h
  have hc := ((poleCoordinate_localInclusion t ht V.frame (a.hom.app (op V.carrier) x)).symm.trans h').trans
    (poleCoordinate_localInclusion t ht V.frame (b.hom.app (op V.carrier) x))
  simpa only [mul_comm (pivotEquation V.frame)] using hc

abbrev poleQuotient := cokernel (twistInclusion t ht)

def poleComplex := ShortComplex.mk (twistInclusion t ht) (cokernel.π _) (cokernel.condition _)

theorem poleShortExact : (poleComplex t ht).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := inclusion_mono t ht
  epi_g := inferInstanceAs (Epi (cokernel.π (twistInclusion t ht)))

/-- Projection of a normalized scalar coefficient to the actual cokernel. -/
def coefficientClass (V : FramedAffine) : Γ(Surface,V.carrier) →+ (poleQuotient t ht).obj.obj (op V.carrier) :=
  ((poleComplex t ht).g.hom.app (op V.carrier)).hom.comp (poleCoordinate t ht V.frame).symm.toAddMonoidHom

theorem coefficientClass_zero_iff (V : FramedAffine) (x : Γ(Surface,V.carrier)) :
    coefficientClass t ht V x = 0 ↔ x ∈ Ideal.span {pivotEquation V.frame} := by
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := sections_exact (poleShortExact t ht) V.carrier ((poleCoordinate t ht V.frame).symm x) hx
    change (twistInclusion t ht).hom.app (op V.carrier) y = _ at hy
    unfold twistInclusion at hy
    rw [extend_apply] at hy
    have h := congrArg (poleCoordinate t ht V.frame) hy
    have h' := ((poleCoordinate_localInclusion t ht V.frame y).symm.trans h).trans
      ((poleCoordinate t ht V.frame).apply_symm_apply x)
    exact Ideal.mem_span_singleton.mpr ⟨_,h'.symm⟩
  · intro hx
    obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hx
    let y := (coordinateEquiv 7 V.frame.chart V.carrier V.frame.within).symm c
    have he : (twistInclusion t ht).hom.app (op V.carrier) y = (poleCoordinate t ht V.frame).symm x := by
      unfold twistInclusion
      rw [extend_apply]
      apply (poleCoordinate t ht V.frame).injective
      refine (poleCoordinate_localInclusion t ht V.frame y).trans ?_
      rw [AddEquiv.apply_symm_apply]
      exact ((congrArg (fun a => pivotEquation V.frame * a)
        ((coordinateEquiv 7 V.frame.chart V.carrier V.frame.within).apply_symm_apply c))).trans hc.symm
    change (poleComplex t ht).g.hom.app _ ((poleCoordinate t ht V.frame).symm x) = 0
    rw [← he]
    exact congrArg (fun f : (poleComplex t ht).X₁ ⟶ (poleComplex t ht).X₃ =>
      f.hom.app (op V.carrier) y) (poleComplex t ht).zero

def localClass (V : FramedAffine) :
    (Γ(Surface,V.carrier) ⧸ (Ideal.span {pivotEquation V.frame}).toAddSubgroup) →+
      (poleQuotient t ht).obj.obj (op V.carrier) :=
  QuotientAddGroup.lift _ (coefficientClass t ht V) (fun x hx => (coefficientClass_zero_iff t ht V x).mpr hx)

private theorem twistHOne_framed (V : FramedAffine) :
    Subsingleton ((addSheaf (ambientTwist 7)).H' 1 V.carrier) := by
  let f : CycleQ2GeometricSheafLocalIso.PatchIso (addSheaf (ambientTwist 7)) (structureAdditiveSheaf Surface)
      V.carrier := {
    app := fun W h => (coordinateEquiv 7 V.frame.chart W (h.trans V.frame.within)).toAddEquiv
    naturality := fun h hW s => CycleQ2LiteralMovingIdealExact.coordinate_restrict 7 V.frame.chart h
      (hW.trans V.frame.within) s }
  exact affineFrameHOne_subsingleton V.affine.isoSpec _ (overIsoOfPatchIso f)

/-- On each original framed affine open the quotient sections are precisely
the coefficients modulo the equation of the orbit divisor. -/
def sectionCoordinateEquiv (V : FramedAffine) :
    (Γ(Surface,V.carrier) ⧸ (Ideal.span {pivotEquation V.frame}).toAddSubgroup) ≃+
      (poleQuotient t ht).obj.obj (op V.carrier) := by
  refine AddEquiv.ofBijective (localClass t ht V) ⟨?_,?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective a
    exact (QuotientAddGroup.eq_zero_iff _).mpr ((coefficientClass_zero_iff t ht V x).mp ha)
  · intro q
    obtain ⟨s,hs⟩ := sections_surjective_of_H_one_subsingleton (poleShortExact t ht) V.carrier
      (twistHOne_framed V) q
    refine ⟨QuotientAddGroup.mk (poleCoordinate t ht V.frame s),?_⟩
    change (poleComplex t ht).g.hom.app _ ((poleCoordinate t ht V.frame).symm (poleCoordinate t ht V.frame s)) = q
    rw [AddEquiv.symm_apply_apply]
    exact hs

theorem sectionCoordinateEquiv_mk (V : FramedAffine) (x : Γ(Surface,V.carrier)) :
    sectionCoordinateEquiv t ht V (QuotientAddGroup.mk x) = coefficientClass t ht V x := rfl

/-- Restrict a representative to a smaller framed affine open, allowing
both its coordinate chart and its pivot to change. -/
theorem coefficientClass_restrict (W V : FramedAffine) (h : V.carrier ≤ W.carrier) (x : Γ(Surface,W.carrier)) :
    (poleQuotient t ht).obj.map (homOfLE h).op (coefficientClass t ht W x) =
      coefficientClass t ht V (((transitionUnit W.frame.chart V.frame.chart V.carrier
        (h.trans W.frame.within) V.frame.within : Γ(Surface,V.carrier)) ^ 7 *
          (orbitTransition (W.frame.restrict h) V.frame : Γ(Surface,V.carrier))) * targetRes h x) := by
  let H := (poleCoordinate t ht W.frame).symm x
  let H' := (PoleForms t).val.map (homOfLE h).op H
  have hcoeff := (poleCoordinate_change t ht (W.frame.restrict h) V.frame H').trans
    (congrArg (fun a : Γ(Surface,V.carrier) =>
      ((transitionUnit W.frame.chart V.frame.chart V.carrier (h.trans W.frame.within) V.frame.within :
        Γ(Surface,V.carrier)) ^ 7 * (orbitTransition (W.frame.restrict h) V.frame : Γ(Surface,V.carrier))) * a)
      (poleCoordinate_restrict t ht W.frame h H).symm)
  rw [show poleCoordinate t ht W.frame H = x from (poleCoordinate t ht W.frame).apply_symm_apply x] at hcoeff
  change (poleQuotient t ht).obj.map _ ((poleComplex t ht).g.hom.app (op W.carrier) H) =
    (poleComplex t ht).g.hom.app (op V.carrier) ((poleCoordinate t ht V.frame).symm _)
  have hn := ConcreteCategory.congr_hom ((poleComplex t ht).g.hom.naturality (homOfLE h).op) H
  refine hn.symm.trans (congrArg ((poleComplex t ht).g.hom.app (op V.carrier)) ?_)
  apply (poleCoordinate t ht V.frame).injective
  rw [AddEquiv.apply_symm_apply]
  exact hcoeff

/-- In the pole sequence this vanishing reduces to the original orbit
quotient because the actual seventh twist has zero first cohomology. -/
theorem poleHOne_subsingleton (h : Subsingleton ((poleQuotient t ht).H' 1 ⊤)) :
    Subsingleton ((addSheaf (PoleForms t)).H' 1 ⊤) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : x.comp (Ext.mk₀ (poleComplex t ht).g) (add_zero 1) = 0 := h.elim _ _
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₂ _ (poleShortExact t ht) x hx
  have hy0 : y = 0 := (CycleQ2LiteralTwistHOne.twist_hOne_subsingleton 7).elim _ _
  exact hy.symm.trans (by rw [hy0, Ext.zero_comp])

end CycleQ2LiteralMovingPoleQuotient
end

#print axioms CycleQ2LiteralMovingPoleQuotient.inclusion_mono
#print axioms CycleQ2LiteralMovingPoleQuotient.poleHOne_subsingleton
