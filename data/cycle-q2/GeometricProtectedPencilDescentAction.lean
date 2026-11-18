import Proposal.GeometricProtectedPencilDescent

/-!
# The order-three action on the descended residue four-form

The cyclic symmetry preserves the sign-fixed field. Its determinant on
the four descended coordinates cancels the character of the normal
coefficient of the protected source.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ProtectedPencilDescent

open HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface CycleQ2AffineDifferentials
  CycleQ2GeometricAffineOverlap CycleQ2ExteriorSectionNaturality CycleQ2ProtectedPencilAction
  CycleQ2ProtectedPencilSourceForm HoldoutConstruction SplitHigherResidue
open CycleQ2AffineWeightedTransfer (u z parameter)

private def gammaHom (ζ : ℂ) (hζ : ζ ^ 3 = 1) : betaFixed →ₐ[ℂ] betaFixed :=
  ((gamma ζ hζ).toAlgHom.comp betaFixed.val).codRestrict betaFixed.toSubalgebra
    (fun x => (beta_gamma_commute ζ hζ x).trans (congrArg (gamma ζ hζ) x.property))

def fixedGamma (ζ : ℂ) (hζ : ζ ^ 3 = 1) : betaFixed ≃ₐ[ℂ] betaFixed :=
  AlgEquiv.ofBijective (gammaHom ζ hζ) ⟨
    fun _ _ e => Subtype.ext ((gamma ζ hζ).injective (congrArg Subtype.val e)),
    fun x => ⟨gammaHom ζ hζ (gammaHom ζ hζ x), Subtype.ext (gamma_cube ζ hζ x)⟩⟩

theorem fixedGamma_val (ζ : ℂ) (hζ : ζ ^ 3 = 1) (x : betaFixed) :
    betaFixed.val (fixedGamma ζ hζ x) = gamma ζ hζ (betaFixed.val x) := rfl

theorem fixedGamma_cube (ζ : ℂ) (hζ : ζ ^ 3 = 1) (x : betaFixed) :
    fixedGamma ζ hζ (fixedGamma ζ hζ (fixedGamma ζ hζ x)) = x :=
  Subtype.ext (gamma_cube ζ hζ x)

attribute [local irreducible] betaFixed
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000

def fixedScale (ζ : ℂ) : Fin 4 → ℂ := ![ζ^2, ζ^2, ζ, 1]

theorem fixedGamma_coordinate (ζ : ℂ) (hζ : ζ ^ 3 = 1) (i : Fin 4) :
    fixedGamma ζ hζ (fixedCoordinates i) =
      algebraMap ℂ betaFixed (fixedScale ζ i) * fixedCoordinates i := by
  apply Subtype.ext
  fin_cases i
  · change gamma ζ hζ (u^2) = algebraMap ℂ K (ζ^2) * u^2
    rw [map_pow, u, gamma_coordinate, mul_pow, map_pow]
  · change gamma ζ hζ (z 2) = algebraMap ℂ K (ζ^2) * z 2
    exact gamma_coordinate ζ hζ 2
  · change gamma ζ hζ (z 3) = algebraMap ℂ K ζ * z 3
    exact gamma_coordinate ζ hζ 3
  · change gamma ζ hζ parameter = algebraMap ℂ K 1 * parameter
    rw [gamma_parameter, map_one, one_mul]

theorem fixedGamma_coefficient (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    fixedGamma ζ hζ fixedCoefficient = algebraMap ℂ betaFixed ζ * fixedCoefficient := by
  apply Subtype.ext
  exact coefficient_character (diagonal (gammaScale ζ)) (gammaScale ζ) (diagonal_X _) (by rfl)
    (gamma ζ hζ).toAlgHom (gamma_affineMap ζ hζ) ζ (gamma_F ζ hζ) (gamma_A ζ hζ)

private theorem halfCoordinateVolume_diagonal {F : Type} [Field F] [Algebra ℂ F]
    (s : Fin 4 → ℂ) (x : Fin 4 → F) :
    halfCoordinateVolume (fun i => algebraMap ℂ F (s i) * x i) =
      coefficientVolume (algebraMap ℂ F (∏ i, s i)) (halfCoordinateVolume x) := by
  have hd (i : Fin 4) : KaehlerDifferential.D ℂ F (algebraMap ℂ F (s i) * x i) =
      algebraMap ℂ F (s i) • KaehlerDifferential.D ℂ F (x i) := by
    rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  unfold halfCoordinateVolume coefficientVolume
  simp_rw [hd]
  rw [AlternatingMap.map_smul_univ, ← map_prod, smul_comm]

theorem fixedGamma_volume (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    exteriorDifferentialMap (fixedGamma ζ hζ).toAlgHom 4 descendedVolume =
      coefficientVolume (algebraMap ℂ betaFixed (ζ^2)) descendedVolume := by
  have hp : (∏ i : Fin 4, fixedScale ζ i) = ζ ^ 2 := by
    rw [Fin.prod_univ_four]
    change ζ ^ 2 * ζ ^ 2 * ζ * 1 = ζ ^ 2
    calc
      _ = ζ ^ 3 * ζ ^ 2 := by ring
      _ = _ := by rw [hζ, one_mul]
  rw [descendedVolume, halfCoordinateVolume_map]
  simp_rw [AlgEquiv.coe_toAlgHom, fixedGamma_coordinate]
  rw [halfCoordinateVolume_diagonal, hp]

private theorem coefficientVolume_comp {F : Type} [Field F] [Algebra ℂ F] (c d : F)
    (ω : ⋀[F]^4 (KaehlerDifferential ℂ F)) :
    coefficientVolume c (coefficientVolume d ω) = coefficientVolume (c * d) ω :=
  smul_smul c d ω

theorem descendedSource_gamma_fixed (ζ : ℂ) (hζ : ζ ^ 3 = 1) :
    exteriorDifferentialMap (fixedGamma ζ hζ).toAlgHom 4 descendedSource = descendedSource := by
  rw [descendedSource, coefficientVolume_map, AlgEquiv.coe_toAlgHom, fixedGamma_coefficient,
    fixedGamma_volume, coefficientVolume_comp, mul_right_comm, ← map_mul,
    show ζ * ζ ^ 2 = 1 by rw [mul_comm, ← pow_succ, hζ], map_one, one_mul]

end CycleQ2ProtectedPencilDescent
end

#print axioms CycleQ2ProtectedPencilDescent.fixedGamma
#print axioms CycleQ2ProtectedPencilDescent.descendedSource_gamma_fixed
