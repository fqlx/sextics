import Proposal.GeometricLiteralMovingPoleComponentsImmersionLocal
import Proposal.GeometricLiteralMovingPoleComponentsDisjoint

/-!
# A kernel frame near each translated curve

Away from the other two images, their defining ideals are the unit ideal.
The orbit pivot therefore generates the actual ideal of the remaining
curve. These neighborhoods cover its image, and the frame on every subopen
is multiplication by the restricted pivot.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingPoleComponents

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace CycleQ2SeedProjectiveImageCocycle
  CycleQ2LiteralMovingResidueBasis CycleQ2LiteralMovingDivisorOrbitFrames
  CycleQ2SeedSectionDivisorTransitions
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricDifferentialSheaf CycleQ2GeometricModuleLocalIso
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra CycleQ2LiteralOrbitAction

abbrev WithinTranslatedCover (W : FramedAffine) (v : Fin 3 → Vertex) : Prop :=
  ∀ b, W.carrier ≤ (closedProjectiveAction (rootValues complexRoot b)
    (rootValues_cube complexRoot complexRoot_quadratic b)).hom ⁻¹ᵁ cover (v b)

abbrev AvoidsOtherComponents (W : FramedAffine) (a : Fin 3) : Prop :=
  ∀ b, b ≠ a → (curveComponent b) ⁻¹ᵁ W.carrier = ⊥

/-- These simultaneous, single-component affine neighborhoods cover the specified image. -/
theorem exists_singleComponentNeighborhood (a : Fin 3)
    (x : CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1) {U : Surface.Opens}
    (hx : (curveComponent a).base x ∈ U) :
    ∃ (W : FramedAffine) (v : Fin 3 → Vertex), (curveComponent a).base x ∈ W.carrier ∧
      W.carrier ≤ U ∧ WithinTranslatedCover W v ∧ AvoidsOtherComponents W a := by
  let imageSet (b : Fin 3) : Set Surface := Set.range (curveComponent b).base
  have imageClosed (b : Fin 3) : IsClosed (imageSet b) := (curveComponent b).isClosedEmbedding.isClosed_range
  let T : Surface.Opens := ⟨(⋃ b : {b : Fin 3 // b ≠ a}, imageSet b.val)ᶜ,
    (isClosed_iUnion_of_finite (fun b : {b : Fin 3 // b ≠ a} => imageClosed b.val)).isOpen_compl⟩
  have hxT : (curveComponent a).base x ∈ T := by
    intro hc
    change (curveComponent a).base x ∈ ⋃ b : {b : Fin 3 // b ≠ a}, imageSet b.val at hc
    obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hc
    exact Set.disjoint_left.mp (components_pairwiseDisjoint b.property.symm) ⟨x,rfl⟩ hb
  obtain ⟨W,v,hxW,hW,hv⟩ := exists_componentNeighborhood (show (curveComponent a).base x ∈ U ⊓ T from ⟨hx,hxT⟩)
  refine ⟨W,v,hxW,hW.trans inf_le_left,hv,?_⟩
  intro b hb
  apply le_antisymm _ bot_le
  intro y hy
  exact ((hW hy).2 (Set.mem_iUnion.mpr ⟨⟨b,hb⟩,y,rfl⟩)).elim

theorem componentKernel_eq_pivot (a : Fin 3) (W : FramedAffine) (v : Fin 3 → Vertex)
    (hv : WithinTranslatedCover W v) (hoff : AvoidsOtherComponents W a) :
    RingHom.ker ((curveComponent a).app W.carrier).hom = pivotIdeal W.frame := by
  have hk (b : Fin 3) : RingHom.ker ((curveComponent b).app W.carrier).hom = componentIdeal W.frame b :=
    componentKernel _ _ W.frame.chart W.carrier W.frame.within (v b) (hv b) W.affine
  rw [hk, pivotIdeal_eq_iInf]
  refine le_antisymm (le_iInf (fun b => ?_)) (iInf_le _ a)
  by_cases hba : b = a
  · subst b
    exact le_rfl
  · have : Subsingleton Γ(CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1,
          (curveComponent b) ⁻¹ᵁ W.carrier) := by rw [hoff b hba]; infer_instance
    rw [← hk b, RingHom.ker_eq_top_of_subsingleton]
    exact le_top

/-- Multiplication by the orbit pivot gives a module-sheaf frame on all subopens. -/
def componentKernelPatchIso (a : Fin 3) (W : FramedAffine) (v : Fin 3 → Vertex)
    (hv : WithinTranslatedCover W v) (hoff : AvoidsOtherComponents W a) :
    PatchIso (SheafOfModules.unit (ringSheaf Surface.sheaf)) (kernelIdealSheaf (curveComponent a))
      W.carrier :=
  pivotKernelPatchIso (curveComponent a) W.frame W.affine (componentKernel_eq_pivot a W v hv hoff)

theorem componentKernelPatchIso_coordinate (a : Fin 3) (W : FramedAffine) (v : Fin 3 → Vertex)
    (hv : WithinTranslatedCover W v) (hoff : AvoidsOtherComponents W a) (O : Surface.Opens)
    (h : O ≤ W.carrier) (r : Γ(Surface,O)) :
    (kernelIdealSectionEquiv (curveComponent a) O
      ((componentKernelPatchIso a W v hv hoff).app O h r) : Γ(Surface,O)) =
      r * CycleQ2SeedSectionSheafGlobal.targetRes h (pivotEquation W.frame) :=
  pivotKernelFrame_coordinate (curveComponent a) W.frame W.affine (componentKernel_eq_pivot a W v hv hoff) h r

/-- The orbit transition is also the actual change of ideal basis on the surviving component. -/
theorem componentKernelPatchIso_change (a : Fin 3) (W V : FramedAffine) (w v : Fin 3 → Vertex)
    (hw : WithinTranslatedCover W w) (hv : WithinTranslatedCover V v)
    (hwo : AvoidsOtherComponents W a) (hvo : AvoidsOtherComponents V a)
    (O : Surface.Opens) (hW : O ≤ W.carrier) (hV : O ≤ V.carrier) (r : Γ(Surface,O)) :
    (componentKernelPatchIso a V v hv hvo).app O hV r =
      (componentKernelPatchIso a W w hw hwo).app O hW
        (r * (orbitTransition (W.frame.restrict hW) (V.frame.restrict hV) : Γ(Surface,O))) := by
  apply (kernelIdealSectionEquiv (curveComponent a) O).injective
  apply Subtype.ext
  rw [componentKernelPatchIso_coordinate, componentKernelPatchIso_coordinate,
    pivotEquation_restrict, pivotEquation_restrict]
  have he : pivotEquation (V.frame.restrict hV) =
      (orbitTransition (W.frame.restrict hW) (V.frame.restrict hV) : Γ(Surface,O)) *
        pivotEquation (W.frame.restrict hW) := orbitTransition_generator _ _
  rw [he, mul_assoc]

end CycleQ2LiteralMovingPoleComponents
end

#print axioms CycleQ2LiteralMovingPoleComponents.exists_singleComponentNeighborhood
#print axioms CycleQ2LiteralMovingPoleComponents.componentKernelPatchIso_coordinate
#print axioms CycleQ2LiteralMovingPoleComponents.componentKernelPatchIso_change
