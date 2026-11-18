import Proposal.GeometricHodgeCyclicTwistMaps
import Proposal.GeometricHodgeCyclicRawFrames
import Proposal.GeometricHodgeNormalCohomology
import Proposal.GeometricAutomorphismCohomology

/-!
# Equivariance of the original projective normal exact sequence

The action on each of its five velocity components uses the intrinsic
linearization of the corresponding coordinate direction. The normal
polynomial uses the degree-six linearization. The chart formula for the
normal map identifies these two actions, so its kernel inherits a
compatible action through the universal property of the kernel.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicNormalSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
  CycleQ2HodgeCyclicAction CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf
  CycleQ2HodgeThreefoldTwist CycleQ2GenericSexticGradient CycleQ2LiteralThreefoldOrbitAction
  CycleQ2HodgeCyclicTwistFrames CycleQ2HodgeCyclicTwistMaps CycleQ2GeometricIncidenceProj
  CycleQ2HodgeTwistRatios
open CycleQ2SeedSectionSheafLimits (sectionProductEquiv sectionProductEquiv_apply sectionProductEquiv_symm_apply)

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (hg : IsUnit (φ goodParameter))

abbrev push := Scheme.Modules.pushforward (g φ z hz)
abbrev actPiece (a : Fin 5) := twistMap φ z hz (geometricWeight a) (char z a)⁻¹ hg
abbrev actNormal := twistMap φ z hz 6 1 hg

def actRaw : raw φ ⟶ (push φ z hz).obj (raw φ) :=
  Pi.lift (fun a => Pi.π (pieces φ) a ≫ actPiece φ z hz hg a) ≫ inv (piComparison (push φ z hz) (pieces φ))

theorem actRaw_projection (a : Fin 5) :
    actRaw φ z hz hg ≫ (push φ z hz).map (Pi.π (pieces φ) a) =
      Pi.π (pieces φ) a ≫ actPiece φ z hz hg a := by
  simp only [actRaw, Category.assoc, inv_piComparison_comp_map_π, Pi.lift_π]

theorem actRaw_value (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (s : Γ(raw φ,V)) :
    let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
    (actRaw φ z hz hg).app V s =
      rawPull φ z hz i V (pre φ z hz V) hi hi' le_rfl s := by
  dsimp only
  let W := pre φ z hz V
  let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
  apply (sectionProductEquiv (pieces φ) W).injective
  funext a
  rw [sectionProductEquiv_apply, sectionProductEquiv_apply]
  apply (chartFrame φ (geometricWeight a) i W hi').injective
  have h := congrArg (fun m : raw φ ⟶ (push φ z hz).obj (pieces φ a) => m.app V s)
    (actRaw_projection φ z hz hg a)
  change (Pi.π (pieces φ) a).app W ((actRaw φ z hz hg).app V s) =
    (actPiece φ z hz hg a).app V ((Pi.π (pieces φ) a).app V s) at h
  rw [h, twistMap_frame φ z hz _ _ hg i V hi]
  simp only [rawPull, sectionProductEquiv_symm_apply, LinearEquiv.apply_symm_apply,
    sectionProductEquiv_apply, Scheme.Hom.appLE_eq_app]
  apply congrArg (fun c => scalar φ W c * _)
  simp only [weight, factor, baseScale, mul_inv_rev, inv_pow, inv_inv]
  ring

include hz in
private theorem char_six (i : Fin 4) : char z i.castSucc ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3*2 by decide, pow_mul, char_cube z hz, one_pow]

private theorem normal_at (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(raw φ,V)) :
    (normalMap φ ≫ actNormal φ z hz hg).app V s =
      (actRaw φ z hz hg ≫ (push φ z hz).map (normalMap φ)).app V s := by
  let W := pre φ z hz V
  let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
  apply (chartFrame φ 6 i W hi').injective
  change chartFrame φ 6 i W _ ((actNormal φ z hz hg).app V ((normalMap φ).app V s)) =
    chartFrame φ 6 i W _ ((normalMap φ).app W ((actRaw φ z hz hg).app V s))
  rw [twistMap_frame φ z hz 6 1 hg i V hi, actRaw_value φ z hz hg i V hi,
    rawPull_normal, Scheme.Hom.appLE_eq_app]
  simp only [weight, one_mul, char_six z hz i, map_one, one_mul]

theorem normal_square : normalMap φ ≫ actNormal φ z hz hg =
    actRaw φ z hz hg ≫ (push φ z hz).map (normalMap φ) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply TopCat.Presheaf.IsSheaf.section_ext ((push φ z hz).obj (twist φ 6)).isSheaf
  intro x hx
  have hxc : x ∈ (⨆ i, U φ i) := by rw [coordinateOpens_cover_of_good φ hg]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxc
  let W := V.unop ⊓ U φ i
  refine ⟨W,inf_le_left,⟨hx,hi⟩,?_⟩
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact normal_at φ z hz hg i W inf_le_right _

def actKernel : rawTangent φ ⟶ (push φ z hz).obj (rawTangent φ) :=
  kernel.lift ((push φ z hz).map (normalMap φ)) (kernel.ι (normalMap φ) ≫ actRaw φ z hz hg)
    (by rw [Category.assoc, ← normal_square, kernel.condition_assoc, zero_comp]) ≫
    (PreservesKernel.iso (push φ z hz) (normalMap φ)).inv

theorem kernel_square : kernel.ι (normalMap φ) ≫ actRaw φ z hz hg =
    actKernel φ z hz hg ≫ (push φ z hz).map (kernel.ι (normalMap φ)) := by
  simp only [actKernel, Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

def normalSequenceMap : normalSequence φ ⟶ (normalSequence φ).map (push φ z hz) where
  τ₁ := actKernel φ z hz hg
  τ₂ := actRaw φ z hz hg
  τ₃ := actNormal φ z hz hg
  comm₁₂ := kernel_square φ z hz hg
  comm₂₃ := normal_square φ z hz hg

end CycleQ2HodgeCyclicNormalSequence
end
#print axioms CycleQ2HodgeCyclicNormalSequence.normalSequenceMap
