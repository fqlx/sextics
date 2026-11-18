import Proposal.GeometricHodgeCyclicTwistFrames
import Proposal.GeometricHodgeNormalDeformations

/-! # Equivariance on the five velocity components of the normal sequence
The coordinate action preserves the native normal morphism on each frame.
On the degree-six normal direction its denominator character is trivial.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicTwistFrames
open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold CycleQ2HodgeCyclicAction
  CycleQ2GeometricIncidenceProj CycleQ2LiteralThreefoldOrbitAction
  CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (i : Fin 4)
variable (V W : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) (hi' : W ≤ coordinateOpen φ i)
  (hWV : W ≤ g φ z hz ⁻¹ᵁ V)

theorem direction_frame (χ : ZMod 3) (a : CycleQ2HodgeInfinitesimalQuotient.Directions ℂ χ) :
    (g φ z hz).appLE V W hWV (chartFrame φ 6 i V hi
      (CycleQ2HodgeNormalDeformations.directionSection φ a V)) =
      scalar φ W (z^χ.val) * chartFrame φ 6 i W hi'
        (CycleQ2HodgeNormalDeformations.directionSection φ a W) := by
  simp only [CycleQ2HodgeNormalDeformations.directionSection, homogeneousSection_coordinate]
  simpa only [baseScale_six z hz, one_mul] using character_pull φ z hz i V W hi hi' hWV χ a.val a.property

open CycleQ2HodgeEulerSheaf (raw pieces normalMap normal_frame)
open CycleQ2SeedSectionSheafLimits (sectionProductEquiv sectionProductEquiv_symm_apply sectionProductEquiv_apply)

def rawPull (s : Γ(raw φ,V)) : Γ(raw φ,W) :=
  (sectionProductEquiv (pieces φ) W).symm fun a => (chartFrame φ _ i W hi').symm
    (scalar φ W (factor z i a)⁻¹ * (g φ z hz).appLE V W hWV
      (chartFrame φ _ i V hi ((sectionProductEquiv (pieces φ) V s) a)))

theorem rawPull_normal (s : Γ(raw φ,V)) :
    chartFrame φ 6 i W hi' ((normalMap φ).app W (rawPull φ z hz i V W hi hi' hWV s)) =
      (g φ z hz).appLE V W hWV (chartFrame φ 6 i V hi ((normalMap φ).app V s)) := by
  rw [normal_frame, normal_frame, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, gradient_pull φ z hz i V W hi hi' hWV]
  simp only [rawPull, sectionProductEquiv_symm_apply, sectionProductEquiv_apply, LinearEquiv.apply_symm_apply]
  ring

end CycleQ2HodgeCyclicTwistFrames
end
#print axioms CycleQ2HodgeCyclicTwistFrames.direction_frame
#print axioms CycleQ2HodgeCyclicTwistFrames.rawPull_normal
