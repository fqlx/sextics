import Proposal.GeometricHodgeEulerVolume
import Proposal.GeometricHodgeGradientAtlas
import Proposal.GeometricLiteralThreefoldDifferentialFrame

/-!
# Trivialization of the canonical sheaf on the good parameter open

On every principal gradient chart the determinant coordinate of the
global three-form is a unit. Multiplication by the three-form therefore
identifies regular functions with three-forms on every open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerVolumeFrame

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
  CycleQ2GeometricDifferentialChartTransport CycleQ2ChartExteriorBinding
  CycleQ2ExteriorSectionNaturality CycleQ2GeometricModuleLocalIso CycleQ2LocalFrameGluing
  CycleQ2LiteralThreefoldDifferentialFrame CycleQ2ExteriorTopBaseChange
  CycleQ2HodgeGradientAtlas CycleQ2HodgeEulerVolume CycleQ2HodgeEulerVolumeChart
  CycleQ2HodgeEulerContractionCharts CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient
open CycleQ2HodgeEuler (F)

private theorem bijective_of_cover {X : Scheme.{0}} {M N : X.Modules} (m : M ⟶ N)
    {I : Type} (D : I → X.Opens) (hD : (⨆ i, D i) = ⊤)
    (hl : ∀ i (W : X.Opens), W ≤ D i → Function.Bijective (m.val.app (op W))) (W : X.Opens) :
    Function.Bijective (m.val.app (op W)) := by
  let e (i : I) : PatchIso M N (D i) :=
    { app O h := LinearEquiv.ofBijective (m.val.app (op O)).hom (hl i O h)
      naturality {O P} h _ s := (PresheafOfModules.naturality_apply m.val (homOfLE h).op s).symm }
  have hc (i j : I) : (e i).Compatible (e j) := fun _ _ _ _ => rfl
  let p := Cover.gluePatchIso M N ⊤ D hD.ge e hc
  have eq : (fun s => (p.app W le_top) s) = fun s => m.val.app (op W) s := by
    funext s
    apply (addSheaf N).eq_of_locally_eq' (fun i => W ⊓ D i) W (fun _ => homOfLE inf_le_left)
      (by rw [← inf_iSup_eq, hD, inf_top_eq])
    intro i
    exact (Cover.mapSection_restrict M N ⊤ D hD.ge e hc W le_top s i).trans
      (PresheafOfModules.naturality_apply m.val (homOfLE (show W ⊓ D i ≤ W from inf_le_left)).op s)
  exact eq ▸ (p.app W le_top).bijective

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))
private abbrev O := SheafOfModules.unit (ringSheaf (threefold φ).sheaf)

theorem omega_on_gradient_subopen (i j : Fin 4) (V : Over (U φ i j)) :
    (threeForms φ).val.map (homOfLE (le_top : V.left ≤ ⊤)).op (omega φ hg) =
      chartExteriorSheafSection (atlas φ i j) (toBase φ) (atlas_overBase φ i j)
        3 V (projectiveResidue (F φ i) i j) := by
  refine ((threeForms φ).val.map_comp_apply
    (homOfLE (le_top : U φ i j ≤ ⊤)).op V.hom.op (omega φ hg)).trans ?_
  rw [omega_on_gradient φ hg i j (U_le φ i j) (atlas φ i j) (atlas_overBase φ i j) (atlas_inv_ι φ i j)]
  exact chartExteriorSheafSection_restrict _ _ _ (toChartTop V) 3 _

private def frame (i j : Fin 4) := frameIso (atlas φ i j) (toBase φ) (atlas_overBase φ i j)
  (basis (F φ i) j)

theorem frame_coordinate_isUnit (i j : Fin 4) (V : Over (U φ i j)) :
    IsUnit (show Γ(threefold φ,V.left) from (frame φ i j).hom.val.app (op V)
      ((threeForms φ).val.map (homOfLE (le_top : V.left ≤ ⊤)).op (omega φ hg))) := by
  rw [omega_on_gradient_subopen, frame, frameIso_on_section, projectiveResidue_eq_frame,
    map_smul, smul_eq_mul, topCoordinate_basis, mul_one]
  exact (volumeUnit φ i j).isUnit.map (CycleQ2GeometricAffineChartSections.chartSection (atlas φ i j) V)

private theorem unit_frame_bijective {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (E : M ≃ₗ[R] R) (y : M) (hy : IsUnit (E y)) : Function.Bijective (fun c : R => c • y) := by
  let J := (LinearEquiv.smulOfUnit hy.unit : R ≃ₗ[R] R).trans E.symm
  have hJ : (J : R → M) = fun c => c • y := by
    funext c
    apply E.injective
    change E (E.symm ((hy.unit : R) * c)) = E (c • y)
    rw [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul, hy.unit_spec, mul_comm]
  exact hJ ▸ J.bijective

def volumeMorphism : O φ ⟶ threeForms φ :=
  (threeForms φ).unitHomEquiv.symm ((threeForms φ).val.sectionsMk
    (fun V => (threeForms φ).val.map (homOfLE (le_top : V.unop ≤ ⊤)).op (omega φ hg))
    (fun _ _ _ => by rw [← (threeForms φ).val.map_comp_apply]; congr 2))

theorem volume_frame (W : (threefold φ).Opens) : Function.Bijective
    (fun c : Γ(threefold φ,W) => c • (threeForms φ).val.map (homOfLE (le_top : W ≤ ⊤)).op (omega φ hg)) := by
  apply bijective_of_cover (volumeMorphism φ hg) (fun a : Fin 4 × Fin 4 => U φ a.1 a.2) (cover φ hg)
  intro a V hV
  let E := ((SheafOfModules.evaluation ((ringSheaf (threefold φ).sheaf).over (U φ a.1 a.2))
    (op (Over.mk (homOfLE hV)))).mapIso (frame φ a.1 a.2)).toLinearEquiv
  exact unit_frame_bijective E _ (frame_coordinate_isUnit φ hg a.1 a.2 (Over.mk (homOfLE hV)))

def volumeIso : O φ ≅ threeForms φ := by
  letI (V : (threefold φ).Opensᵒᵖ) : IsIso ((volumeMorphism φ hg).val.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (volume_frame φ hg V.unop)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => asIso ((volumeMorphism φ hg).val.app V))
      (fun {_ _} f => (volumeMorphism φ hg).val.naturality f))

theorem volumeIso_hom_apply (W : (threefold φ).Opens) (c : Γ(threefold φ,W)) :
    (volumeIso φ hg).hom.val.app (op W) c =
      c • (threeForms φ).val.map (homOfLE (le_top : W ≤ ⊤)).op (omega φ hg) := rfl

end CycleQ2HodgeEulerVolumeFrame
end

#print axioms CycleQ2HodgeEulerVolumeFrame.volume_frame
#print axioms CycleQ2HodgeEulerVolumeFrame.volumeIso_hom_apply
