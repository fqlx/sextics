import Proposal.GeometricLiteralMovingPoleComponentsCRT
import Proposal.GeometricLiteralMovingPoleComponentsImmersion
import Proposal.GeometricLiteralMovingPoleQuotient

/-!
# Local coefficients of the pole quotient on the three curves

On each simultaneous affine neighborhood the actual pole quotient has three
curve coefficients. Restriction pulls back the twist and divisor frame
transition to each immersed component.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingPoleComponents

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat.Presheaf
  Opposite AlgebraicGeometry CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionAffineInjective CycleQ2SeedSectionDivisorTransitions
  CycleQ2SeedSectionSheafGlobal CycleQ2LiteralMovingResidueBasis
  CycleQ2LiteralMovingPoleQuotient CycleQ2LiteralOrbitAction
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeCartierFrames CycleQ2LiteralMovingDivisorOrbitFrames
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2CartierSurfaceGrading
  CycleQ2SeedCyclicAction

private abbrev indexedImmersion (a : Fin 3) := componentImmersion (rootValues complexRoot a)
  (rootValues_cube complexRoot complexRoot_quadratic a)

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

section Affine
variable (W : FramedAffine) (v : Fin 3 → Vertex)
  (hv : ∀ a, W.carrier ≤ (closedProjectiveAction (rootValues complexRoot a)
    (rootValues_cube complexRoot complexRoot_quadratic a)).hom ⁻¹ᵁ cover (v a))

/-- In a simultaneous affine frame the three pole coefficients are actual sections on
    the inverse images of the three translated curve immersions. -/
def poleAffineComponents : (poleQuotient t ht).obj.obj (op W.carrier) ≃+
    (∀ a, Γ(CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1, (indexedImmersion a) ⁻¹ᵁ W.carrier)) :=
  ((sectionCoordinateEquiv t ht W).symm.trans (components W.frame).toRingEquiv.toAddEquiv).trans
    (AddEquiv.piCongrRight (fun a =>
      (componentQuotientEquiv _ (rootValues_cube complexRoot complexRoot_quadratic a)
        W.frame.chart W.carrier W.frame.within (v a) (hv a) W.affine).toAddEquiv))

theorem poleAffineComponents_coefficient (r : Γ(Surface,W.carrier)) (a : Fin 3) :
    poleAffineComponents t ht W v hv (coefficientClass t ht W r) a = (indexedImmersion a).app W.carrier r := by
  rw [← sectionCoordinateEquiv_mk]
  simp only [poleAffineComponents, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact componentQuotientEquiv_mk _ (rootValues_cube complexRoot complexRoot_quadratic a)
    W.frame.chart W.carrier W.frame.within (v a) (hv a) W.affine r

/-- Restriction in the pole quotient acts on each curve coefficient by the pullback
    of the seventh-power coordinate transition and the orbit pivot transition. -/
theorem poleAffineComponents_restrict (V : FramedAffine) (w : Fin 3 → Vertex)
    (hw : ∀ a, V.carrier ≤ (closedProjectiveAction (rootValues complexRoot a)
      (rootValues_cube complexRoot complexRoot_quadratic a)).hom ⁻¹ᵁ cover (w a))
    (h : V.carrier ≤ W.carrier) (s : (poleQuotient t ht).obj.obj (op W.carrier)) (a : Fin 3) :
    poleAffineComponents t ht V w hw ((poleQuotient t ht).obj.map (homOfLE h).op s) a =
      (indexedImmersion a).app V.carrier (((transitionUnit W.frame.chart V.frame.chart V.carrier
        (h.trans W.frame.within) V.frame.within : Γ(Surface,V.carrier)) ^ 7) *
          (orbitTransition (W.frame.restrict h) V.frame : Γ(Surface,V.carrier))) *
      (CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1).presheaf.map
        (homOfLE ((indexedImmersion a).preimage_mono h)).op (poleAffineComponents t ht W v hv s a) := by
  obtain ⟨q,rfl⟩ := (sectionCoordinateEquiv t ht W).surjective s
  obtain ⟨r,rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [sectionCoordinateEquiv_mk, coefficientClass_restrict, poleAffineComponents_coefficient,
    poleAffineComponents_coefficient, map_mul]
  apply congrArg (_ * ·)
  exact ConcreteCategory.congr_hom ((indexedImmersion a).naturality (homOfLE h).op) r

include v hv in
theorem quotient_sections_off (hempty : ∀ a, (indexedImmersion a) ⁻¹ᵁ W.carrier = ⊥) :
    Subsingleton ((poleQuotient t ht).obj.obj (op W.carrier)) := by
  have h (a : Fin 3) : Subsingleton Γ(CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1,
      (indexedImmersion a) ⁻¹ᵁ W.carrier) := by rw [hempty]; infer_instance
  exact (poleAffineComponents t ht W v hv).injective.subsingleton

end Affine

end CycleQ2LiteralMovingPoleComponents
end

#print axioms CycleQ2LiteralMovingPoleComponents.poleAffineComponents_restrict
