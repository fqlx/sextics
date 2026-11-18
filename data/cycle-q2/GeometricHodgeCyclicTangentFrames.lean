import Proposal.GeometricHodgeCyclicNormalSequence
import Proposal.GeometricHodgeCyclicResidue
import Proposal.GeometricHodgeEulerTangentDescent

/-! # Transport of actual tangent derivatives on the projective coordinates

The order-three action on the five ambient velocity components descends
in the normalized Euler frame to conjugation of the actual tangent
derivation on each retained coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicTangentFrames

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
  CycleQ2HodgeCyclicNormalSequence CycleQ2HodgeCyclicTwistFrames CycleQ2HodgeCyclicTwistMaps
  CycleQ2HodgeCyclicAction CycleQ2HodgeEulerTangentDescent CycleQ2HodgeEulerTangentToQuotient
  CycleQ2HodgeEulerQuotientSections CycleQ2HodgeEulerQuotientFrames CycleQ2HodgeTwistRatios
  CycleQ2GeometricIncidenceProj CycleQ2HodgeEulerTangentValues
  CycleQ2SeedSectionSheafLimits
open CycleQ2GenericSexticGradient (CoeffRing)

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (hg : IsUnit (φ goodParameter))

def toTangent := cokernel.π (radialTangent φ) ≫ (quotientTangentIso φ hg).hom

theorem value (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (v : Γ(rawTangent φ,V)) (b : Fin 4) :
    values φ i V hi ((toTangent φ hg).app V v) (i.castSucc.succAbove b) =
      rawCoordinate φ i V hi (i.castSucc.succAbove b) v -
      rawCoordinate φ i V hi i.castSucc v * euler φ i V hi (i.castSucc.succAbove b) := by
  rw [← frame_toQuotient, ← tangentToQuotient_app φ hg]
  have he : toTangent φ hg ≫ tangentToQuotient φ hg = cokernel.π (radialTangent φ) := by
    change (_ ≫ (quotientTangentIso φ hg).hom) ≫ (quotientTangentIso φ hg).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (frame φ i V hi ((toTangent φ hg ≫ tangentToQuotient φ hg).app V v)).val b = _
  rw [he, frame_project_apply]

theorem rawCoordinate_pull (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (v : Γ(rawTangent φ,V)) (a : Fin 5) :
    let W := pre φ z hz V
    let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
    rawCoordinate φ i W hi' a ((actKernel φ z hz hg).app V v) =
      scalar φ W (factor z i a)⁻¹ * (g φ z hz).app V (rawCoordinate φ i V hi a v) := by
  dsimp only
  let W := pre φ z hz V
  let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
  have hk := congrArg (fun m : rawTangent φ ⟶ (push φ z hz).obj (raw φ) => m.app V v)
    (kernel_square φ z hz hg)
  change (actRaw φ z hz hg).app V ((kernel.ι _).app V v) =
    (kernel.ι _).app W ((actKernel φ z hz hg).app V v) at hk
  change (chartFrame φ _ i W hi') ((Pi.π _ a).app W ((kernel.ι _).app W _)) = _
  rw [← hk, actRaw_value φ z hz hg i V hi]
  rw [rawPull, sectionProductEquiv_symm_apply, LinearEquiv.apply_symm_apply, Scheme.Hom.appLE_eq_app,
    sectionProductEquiv_apply]
  rfl

private theorem euler_pull (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (a : Fin 5) :
    let W := pre φ z hz V
    let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
    (g φ z hz).app V (euler φ i V hi a) = scalar φ W (factor z i a) * euler φ i W hi' a := by
  dsimp only
  let W := pre φ z hz V
  let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
  have h := coordinate_pull φ z hz i V W hi hi' le_rfl a
  rw [Scheme.Hom.appLE_eq_app] at h
  rw [euler, map_mul, map_natCast, h, euler]
  ring

theorem normalized_value (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (v : Γ(rawTangent φ,V)) (b : Fin 4) :
    let W := pre φ z hz V
    let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
    values φ i W hi' ((toTangent φ hg).app W ((actKernel φ z hz hg).app V v)) (i.castSucc.succAbove b) =
      scalar φ W (chartFactor z i b)⁻¹ *
        (g φ z hz).app V (values φ i V hi ((toTangent φ hg).app V v) (i.castSucc.succAbove b)) := by
  dsimp only
  let W := pre φ z hz V
  let a := i.castSucc.succAbove b
  have hunit : scalar φ W (factor z i a)⁻¹ * scalar φ W (factor z i a) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (CycleQ2HodgeCyclicAction.chartFactor_ne_zero z hz i b), map_one]
  rw [value, value, rawCoordinate_pull, rawCoordinate_pull, factor_self z hz i, inv_one, map_one,
    one_mul, map_sub, map_mul, euler_pull]
  change _ - _ = scalar φ W (factor z i a)⁻¹ * _
  linear_combination hunit * (g φ z hz).app V (rawCoordinate φ i V hi i.castSucc v) *
    euler φ i W _ a

/-- Conjugation on an actual differential of each affine coordinate. -/
theorem coordinate_derivation (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (v : Γ(rawTangent φ,V)) (b : Fin 4) :
    let W := pre φ z hz V
    let a := i.castSucc.succAbove b
    sectionD (toBase φ) ((toTangent φ hg).app W ((actKernel φ z hz hg).app V v))
      ((g φ z hz).app V (coordinateSection φ i V hi a)) =
      (g φ z hz).app V (values φ i V hi ((toTangent φ hg).app V v) a) := by
  dsimp only
  let W := pre φ z hz V
  let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
  let a := i.castSucc.succAbove b
  let c := chartFactor z i b
  letI := nativeAlgebra (toBase φ) W
  let D := sectionD (toBase φ) ((toTangent φ hg).app W ((actKernel φ z hz hg).app V v))
  have h := coordinate_pull φ z hz i V W hi hi' le_rfl a
  rw [Scheme.Hom.appLE_eq_app] at h
  change D ((g φ z hz).app V (coordinateSection φ i V hi a)) = _
  rw [h]
  change D (algebraMap ℂ Γ(threefold φ,W) c * coordinateSection φ i W hi' a) = _
  rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  change scalar φ W c * values φ i W hi' _ a = _
  rw [normalized_value φ z hz hg i V hi v b, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (chartFactor_ne_zero z hz i b), map_one, one_mul]

end CycleQ2HodgeCyclicTangentFrames
end
#print axioms CycleQ2HodgeCyclicTangentFrames.normalized_value
