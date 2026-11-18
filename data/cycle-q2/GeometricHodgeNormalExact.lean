import Proposal.GeometricHodgeEulerSheaf
import Proposal.GeometricHodgeThreefoldGradient
import Proposal.GeometricHodgeThreefoldProper
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Surjectivity of the normal map of the full-family hypersurface

On the actual gradient open, the five normalized normal coefficients
generate the unit ideal on each weight-one coordinate patch. In the
twist frames they lift every section of O(6) on each smaller open.
The global normal map is therefore an epimorphism of module sheaves.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerSheaf

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2SeedSectionSheafLimits (sectionProductEquiv sectionProductEquiv_symm_apply)
open CycleQ2GenericSexticGradient (CoeffRing gradientOpen)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

theorem normal_unit_of_span (i : Fin 4)
    (hspan : Ideal.span (Set.range (CycleQ2HodgeEuler.conePartial φ i)) = ⊤)
    (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    ∃ c : Fin 5 → Γ(threefold φ,V), ∑ j, c j * normalized φ i (partialValue φ j) (partial_mem φ j) V hi = 1 := by
  obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hspan)
  let e := CycleQ2HodgeEulerChartBinding.chartEquiv φ i
  have hj (j : Fin 5) : e.symm (CycleQ2HodgeEuler.conePartial φ i j) = CycleQ2HodgeEulerChartBinding.gradientRatio φ i j :=
    e.symm_apply_eq.mpr (CycleQ2HodgeEulerChartBinding.chartEquiv_gradientRatio φ i j).symm
  refine ⟨fun j => sectionMap φ i V hi (e.symm (c j)), ?_⟩
  have h := congrArg (fun a => sectionMap φ i V hi (e.symm a)) hc
  simpa only [map_sum, map_mul, map_one, hj, sectionMap_gradient] using h

theorem normal_section_surjective_of_span (i : Fin 4)
    (hspan : Ideal.span (Set.range (CycleQ2HodgeEuler.conePartial φ i)) = ⊤)
    (V : (threefold φ).Opens) (hi : V ≤ U φ i) : Function.Surjective ((normalMap φ).app V) := by
  intro s
  obtain ⟨c,hc⟩ := normal_unit_of_span φ i hspan V hi
  let a (j : Fin 5) : Γ(pieces φ j,V) := (chartFrame φ _ i V hi).symm (c j * chartFrame φ 6 i V hi s)
  refine ⟨(sectionProductEquiv (pieces φ) V).symm a, (chartFrame φ 6 i V hi).injective ?_⟩
  rw [normal_frame]
  simp only [sectionProductEquiv_symm_apply, a, LinearEquiv.apply_symm_apply]
  calc
    _ = (∑ j, c j * normalized φ i (partialValue φ j) (partial_mem φ j) V hi) *
        chartFrame φ 6 i V hi s := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = _ := by rw [hc, one_mul]

theorem normal_section_surjective (hg : IsUnit (φ gradientOpen)) (i : Fin 4)
    (V : (threefold φ).Opens) (hi : V ≤ U φ i) : Function.Surjective ((normalMap φ).app V) :=
  normal_section_surjective_of_span φ i (conePartial_span φ hg i) V hi

theorem normal_additive_epi_of_span (hv : IsUnit (φ vertexCoefficient))
    (hspan : ∀ i, Ideal.span (Set.range (CycleQ2HodgeEuler.conePartial φ i)) = ⊤) :
    Epi ((SheafOfModules.toSheaf (threefold φ).ringCatSheaf).map (normalMap φ)) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro V s x hx
  have hxc : x ∈ ⨆ i : Fin 4, U φ i := by rw [coordinateOpens_cover φ hv]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxc
  exact ⟨V ⊓ U φ i, inf_le_left,
    normal_section_surjective_of_span φ i (hspan i) _ inf_le_right _, ⟨hx,hi⟩⟩

theorem normal_additive_epi (hg : IsUnit (φ goodParameter)) :
    Epi ((SheafOfModules.toSheaf (threefold φ).ringCatSheaf).map (normalMap φ)) := by
  rw [goodParameter, map_mul, IsUnit.mul_iff] at hg
  exact normal_additive_epi_of_span φ hg.2 (conePartial_span φ hg.1)

theorem normal_epi (hg : IsUnit (φ goodParameter)) : Epi (normalMap φ) :=
  Functor.epi_of_epi_map _ (normal_additive_epi φ hg)

theorem normalized_radial_self (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    (geometricWeight i.castSucc : Γ(threefold φ,V)) *
      normalized φ i (coord φ i.castSucc) (coord_mem_grade φ i.castSucc) V hi = 1 := by
  let e := CycleQ2HodgeEulerChartBinding.chartEquiv φ i
  have h : (geometricWeight i.castSucc : ChartRing φ i) *
      CycleQ2HodgeEulerChartBinding.ratio φ i i.castSucc = 1 := by
    apply e.injective
    simp only [map_mul, map_natCast, map_one, e, CycleQ2HodgeEulerChartBinding.chartEquiv_ratio]
    exact CycleQ2HodgeEuler.radial_self φ i
  simpa only [map_mul, map_natCast, map_one, sectionMap_coordinate] using congrArg (sectionMap φ i V hi) h

theorem radial_section_injective (V : (threefold φ).Opens) : Function.Injective ((radialMap φ).app V) := by
  intro s t h
  apply CycleQ2HodgeAtlasLine.component_injective (cocycle φ 0) V
  intro i
  have hh := congrArg (fun z : Γ(raw φ,V) =>
    CycleQ2HodgeAtlasLine.component (cocycle φ (geometricWeight i.castSucc)) i V
      ((Pi.π (pieces φ) i.castSucc).app V z)) h
  simpa only [radial_component, normalized_radial_self, one_mul] using hh

instance : Mono (radialMap φ) where
  right_cancellation {M} f g h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro O
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact radial_section_injective φ O.unop (congrArg (fun j : M ⟶ raw φ => j.app O.unop s) h)

abbrev rawTangent := kernel (normalMap φ)

def radialTangent : twist φ 0 ⟶ rawTangent φ := kernel.lift _ _ (radial_normal φ)

instance : Mono (radialTangent φ) := by
  have h : radialTangent φ ≫ kernel.ι (normalMap φ) = radialMap φ := kernel.lift_ι _ _ _
  letI : Mono (radialTangent φ ≫ kernel.ι (normalMap φ)) := by rw [h]; infer_instance
  exact mono_of_mono (radialTangent φ) (kernel.ι (normalMap φ))

abbrev tangentQuotient := cokernel (radialTangent φ)

def normalSequence := ShortComplex.mk (kernel.ι (normalMap φ)) (normalMap φ) (kernel.condition _)
def eulerSequence := ShortComplex.mk (radialTangent φ) (cokernel.π (radialTangent φ)) (cokernel.condition _)

theorem normalSequence_exact (hg : IsUnit (φ goodParameter)) : (normalSequence φ).ShortExact := by
  letI := normal_epi φ hg
  exact { exact := ShortComplex.exact_kernel (normalMap φ) }

theorem eulerSequence_exact : (eulerSequence φ).ShortExact :=
  { exact := ShortComplex.exact_cokernel (radialTangent φ) }

end CycleQ2HodgeEulerSheaf
end

#print axioms CycleQ2HodgeEulerSheaf.normalSequence_exact
#print axioms CycleQ2HodgeEulerSheaf.eulerSequence_exact
