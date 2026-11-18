import Proposal.GeometricHodgeEulerQuotientSections
import Proposal.GeometricHodgeEulerSequence

/-! On every subopen of a weight-one chart, the genuine projective
Euler cokernel has the normalized four-vector gradient presentation.
The projection formula records every homogeneous tangent coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerQuotientFrames

open AlgebraicGeometry CategoryTheory Limits Opposite
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricIncidenceProj
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios CycleQ2HodgeAtlasLine
open CycleQ2HodgeEulerSheaf CycleQ2HodgeEulerQuotientSections
open CycleQ2SeedSectionSheafLimits
open CycleQ2HodgeEulerRestrictedCokernel (sectionLinear linearQuotient linearQuotient_mk)
open CycleQ2HodgeEuler (pairing pairing_apply normalize tangentProjection tangentProjection_surj)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4)
  (V : (threefold φ).Opens) (hi : V ≤ U φ i)

abbrev gradients (j : Fin 5) := normalized φ i (partialValue φ j) (partial_mem φ j) V hi
abbrev euler (j : Fin 5) := (geometricWeight j : Γ(threefold φ,V)) *
  normalized φ i (coord φ j) (coord_mem_grade φ j) V hi

theorem euler_zero : pairing (gradients φ i V hi) (euler φ i V hi) = 0 :=
  (pairing_apply _ _).trans (normalized_euler φ i V hi)

private def ambientMap : Γ(rawTangent φ,V) →ₗ[Γ(threefold φ,V)] (Fin 5 → Γ(threefold φ,V)) :=
  LinearMap.pi (rawCoordinate φ i V hi)

private theorem ambient_zero (s : Γ(rawTangent φ,V)) : pairing (gradients φ i V hi) (ambientMap φ i V hi s) = 0 := by
  have hk := congrArg (fun m : rawTangent φ ⟶ twist φ 6 => m.app V s) (kernel.condition (normalMap φ))
  change (normalMap φ).app V ((kernel.ι (normalMap φ)).app V s) = 0 at hk
  have hs := normal_frame φ i V hi ((kernel.ι (normalMap φ)).app V s)
  rw [hk, map_zero] at hs
  exact (pairing_apply _ _).trans hs.symm

def ambientEquiv : Γ(rawTangent φ,V) ≃ₗ[Γ(threefold φ,V)] (pairing (gradients φ i V hi)).ker := by
  let m := (ambientMap φ i V hi).codRestrict (pairing (gradients φ i V hi)).ker
    (ambient_zero φ i V hi)
  apply LinearEquiv.ofBijective m
  constructor
  · intro a b hab
    apply (sectionKernelEquiv (normalMap φ) V).injective
    apply Subtype.ext
    rw [sectionKernelEquiv_val, sectionKernelEquiv_val]
    apply (sectionProductEquiv (pieces φ) V).injective
    funext j
    rw [sectionProductEquiv_apply, sectionProductEquiv_apply]
    apply (chartFrame φ (geometricWeight j) i V hi).injective
    exact congrFun (congrArg Subtype.val hab) j
  · intro w
    let t := (sectionProductEquiv (pieces φ) V).symm
      (fun j => (chartFrame φ (geometricWeight j) i V hi).symm (w.val j))
    have ht : (normalMap φ).app V t = 0 := by
      apply (chartFrame φ 6 i V hi).injective
      rw [normal_frame, map_zero]
      simp only [t, sectionProductEquiv_symm_apply, LinearEquiv.apply_symm_apply]
      exact (pairing_apply _ _).symm.trans w.property
    refine ⟨(sectionKernelEquiv (normalMap φ) V).symm ⟨t, ht⟩, Subtype.ext ?_⟩
    funext j
    change chartFrame φ (geometricWeight j) i V hi ((Pi.π (pieces φ) j).app V
      ((kernel.ι (normalMap φ)).app V ((sectionKernelEquiv (normalMap φ) V).symm ⟨t, ht⟩))) = w.val j
    rw [sectionKernelEquiv_symm_val]
    simp only [t, sectionProductEquiv_symm_apply, LinearEquiv.apply_symm_apply]

theorem ambientEquiv_apply (s : Γ(rawTangent φ,V)) (j : Fin 5) :
    (ambientEquiv φ i V hi s).val j = rawCoordinate φ i V hi j s := rfl

theorem ambientEquiv_radial (s : Γ(twist φ 0,V)) :
    (ambientEquiv φ i V hi ((radialTangent φ).app V s)).val =
      (chartFrame φ 0 i V hi s) • euler φ i V hi := by
  funext j
  have hk : (kernel.ι (normalMap φ)).app V ((radialTangent φ).app V s) = (radialMap φ).app V s :=
    congrArg (fun m : twist φ 0 ⟶ raw φ => m.app V s) (kernel.lift_ι _ _ (radial_normal φ))
  change chartFrame φ (geometricWeight j) i V hi ((Pi.π (pieces φ) j).app V
    ((kernel.ι (normalMap φ)).app V ((radialTangent φ).app V s))) =
    (chartFrame φ 0 i V hi s) * euler φ i V hi j
  rw [hk]
  have hh := congrArg (restrictRing (X := threefold φ) (le_inf le_rfl hi)) (radial_component φ j i V s)
  have hr : restrictRing (X := threefold φ) (le_inf le_rfl hi)
      (normalized φ i (coord φ j) (coord_mem_grade φ j) (V ⊓ U φ i) inf_le_right) =
      normalized φ i (coord φ j) (coord_mem_grade φ j) V hi :=
    normalized_restrict φ i (coord φ j) (coord_mem_grade φ j) inf_le_right (le_inf le_rfl hi)
  rw [map_mul, map_mul, map_natCast, hr] at hh
  exact hh.trans (mul_comm _ _)

def projection : Γ(rawTangent φ,V) →ₗ[Γ(threefold φ,V)]
    (pairing (gradients φ i V hi ∘ i.castSucc.succAbove)).ker :=
  (tangentProjection i.castSucc _ (euler φ i V hi) (normalized_radial_self φ i V hi) (euler_zero φ i V hi)).comp
    (ambientEquiv φ i V hi).toLinearMap

theorem projection_apply (v : Γ(rawTangent φ,V)) (j : Fin 4) :
    (projection φ i V hi v).val j = rawCoordinate φ i V hi (i.castSucc.succAbove j) v -
      rawCoordinate φ i V hi i.castSucc v * euler φ i V hi (i.castSucc.succAbove j) := rfl

theorem projection_surjective : Function.Surjective (projection φ i V hi) :=
  (tangentProjection_surj i.castSucc (gradients φ i V hi) (euler φ i V hi)
    (normalized_radial_self φ i V hi) (euler_zero φ i V hi)).comp (ambientEquiv φ i V hi).surjective

theorem radial_range :
    (sectionLinear (radialTangent φ) V).range =
      (projection φ i V hi).ker := by
  ext v
  have he := CycleQ2HodgeEuler.radial_range_eq_ker i.castSucc (gradients φ i V hi) (euler φ i V hi)
    (normalized_radial_self φ i V hi) (euler_zero φ i V hi)
  constructor
  · rintro ⟨s, rfl⟩
    change ambientEquiv φ i V hi ((radialTangent φ).app V s) ∈
      (tangentProjection i.castSucc (gradients φ i V hi) (euler φ i V hi)
        (normalized_radial_self φ i V hi) (euler_zero φ i V hi)).ker
    rw [← he]
    exact ⟨chartFrame φ 0 i V hi s, Subtype.ext (ambientEquiv_radial φ i V hi s).symm⟩
  · intro hv
    change ambientEquiv φ i V hi v ∈
      (tangentProjection i.castSucc (gradients φ i V hi) (euler φ i V hi)
        (normalized_radial_self φ i V hi) (euler_zero φ i V hi)).ker at hv
    rw [← he] at hv
    obtain ⟨a, ha⟩ := hv
    refine ⟨(chartFrame φ 0 i V hi).symm a, (ambientEquiv φ i V hi).injective (Subtype.ext ?_)⟩
    rw [ambientEquiv_radial, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val ha

/-- All sections of the native cokernel are the normalized four-tuples tangent to the sextic. -/
def frame : Γ(tangentQuotient φ,V) ≃ₗ[Γ(threefold φ,V)]
    (pairing (gradients φ i V hi ∘ i.castSucc.succAbove)).ker :=
  (quotientEquiv φ i V hi).symm.trans
    (linearQuotient (projection φ i V hi) _ (radial_range φ i V hi) (projection_surjective φ i V hi))

@[simp] theorem frame_project (v : Γ(rawTangent φ,V)) :
    frame φ i V hi ((cokernel.π (radialTangent φ)).app V v) = projection φ i V hi v := by
  rw [← quotientEquiv_mk φ i V hi]
  simp only [frame, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, linearQuotient_mk]

/-- In the quotient frame the pivot entry is removed by subtracting its
multiple of the Euler vector from each of the four retained entries. -/
theorem frame_project_apply (v : Γ(rawTangent φ,V)) (j : Fin 4) :
    (frame φ i V hi ((cokernel.π (radialTangent φ)).app V v)).val j =
      rawCoordinate φ i V hi (i.castSucc.succAbove j) v -
        rawCoordinate φ i V hi i.castSucc v * euler φ i V hi (i.castSucc.succAbove j) := by
  rw [frame_project, projection_apply]

end CycleQ2HodgeEulerQuotientFrames
end
#print axioms CycleQ2HodgeEulerQuotientFrames.frame
#print axioms CycleQ2HodgeEulerQuotientFrames.frame_project_apply
