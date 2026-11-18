import Proposal.GeometricHodgeCyclicVolume
import Proposal.GeometricHodgeGlobalFunctions
import Proposal.GeometricHodgeEulerVolumeFrame
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # The moving threefold has no invariant global three-forms

The projective residue trivializes the top exterior sheaf. Its global
multipliers are complex constants, so every global three-form has the
same nontrivial character as the volume itself.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicTopForms
open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricHodgeThreefold
  CycleQ2HodgeCyclicAction CycleQ2GeometricDifferentialSheaf CycleQ2HodgeCyclicSheafResidue
  CycleQ2HodgeEulerVolume CycleQ2LiteralAbelJacobiQPullback CycleQ2ExteriorPullComposition
open CycleQ2GenericSexticGradient (CoeffRing)

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter)) (z : ℂ) (hz : z^3=1)
abbrev actionOnForms := onSections (action φ z hz).hom (pulling φ z hz 3) ⊤
abbrev scalar := coefficientOn (threefold φ).sheaf (κ φ) ⊤

theorem character (s : Γ(threeForms φ,⊤)) :
    actionOnForms φ z hz s = scalar φ (z^2) • s := by
  obtain ⟨f,hf⟩ := (CycleQ2HodgeEulerVolumeFrame.volume_frame φ hg ⊤).surjective s
  have htop : (threeForms φ).val.map (homOfLE (le_top : (⊤ : (threefold φ).Opens) ≤ ⊤)).op (omega φ hg) =
      omega φ hg := ConcreteCategory.congr_hom ((threeForms φ).val.presheaf.map_id (op ⊤)) (omega φ hg)
  change f • _ = s at hf
  rw [htop] at hf
  have hv := hg
  rw [goodParameter, map_mul, IsUnit.mul_iff] at hv
  obtain ⟨b,hb⟩ := CycleQ2HodgeGlobalFunctions.globalFunction φ hv.2 f
  rw [← hf, hb, map_smulₛₗ]
  change (action φ z hz).hom.app ⊤ (scalar φ b) • (pulling φ z hz 3).val.app (op ⊤) (omega φ hg) = _
  rw [compatible_over _ _ _ (action_overBase φ z hz) ⊤ b, CycleQ2HodgeCyclicVolume.omega_pull]
  exact smul_comm _ _ _

theorem fixed_eq_zero (s : Γ(threeForms φ,⊤))
    (hs : ∀ (z : ℂ) (hz : z^3=1), actionOnForms φ z hz s = s) : s = 0 := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))
  have hp : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have hn : ζ^2 ≠ 1 := hp.pow_ne_one_of_pos_of_lt (by decide) (by decide)
  have h := hs ζ hp.pow_eq_one
  rw [character φ hg] at h
  have he : scalar φ (ζ^2-1) • s = 0 := by rw [map_sub, map_one, sub_smul, one_smul, h, sub_self]
  have hu := (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hn)).map (scalar φ)
  exact (IsUnit.smul_left_cancel hu).mp (he.trans (smul_zero _).symm)

end CycleQ2HodgeCyclicTopForms
end
#print axioms CycleQ2HodgeCyclicTopForms.fixed_eq_zero
