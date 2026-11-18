import Proposal.GeometricProtectedPencilAction
import Proposal.GeometricSurfaceResidueOverlap

/-!
# Symmetries of the protected affine residue four-form

On the protected chart the transverse coordinate is fixed. Differentiating
in this coordinate preserves the numerator character and the invariant
denominator jets. The four genuine Kähler differentials contribute the
determinant of the action on the remaining chart coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ProtectedPencilSourceForm

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineDifferentials CycleQ2AffineExterior CycleQ2AffineExactness
  CycleQ2AffineResidueClosure CycleQ2GeometricAffineOverlap CycleQ2ExteriorSectionNaturality
  HoldoutConstruction SplitHigherResidue

section Diagonal

variable (A : AmbientPoly 4 →ₐ[ℂ] AmbientPoly 4) (s : Fin 5 → ℂ)
    (hX : ∀ i, A (X i) = C (s i) * X i) (hs : s 0 = 1)

include hX hs in
theorem diagonal_normalDerivative (p : AmbientPoly 4) :
    A (pderiv 0 p) = pderiv 0 (A p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [pderiv_C, map_zero, show A (C c) = C c from A.commutes c, pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    have hj : A (pderiv 0 (X j)) = pderiv 0 (A (X j)) := by
      rw [hX, pderiv_C_mul]
      by_cases h : j = 0
      · subst j
        rw [pderiv_X_self, hs, map_one, map_one, one_mul]
      · rw [pderiv_X_of_ne h, map_zero, mul_zero]
    simp only [map_mul, pderiv_mul, map_add, hp, hj]

variable (φ : K →ₐ[ℂ] K) (hφ : ∀ p : AmbientPoly 4, φ (affineMap p) = affineMap (A p))

include hφ hX in
theorem volume_character :
    exteriorDifferentialMap φ 4 volume = algebraMap ℂ K (∏ j : Fin 4, s j.succ) • volume := by
  have hd (j : Fin 4) : differentialMap φ (coordinateDifferential j) =
      algebraMap ℂ K (s j.succ) • coordinateDifferential j := by
    rw [coordinateDifferential, differentialMap_D, hφ, hX, map_mul, affineMap_constant,
      Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  rw [volume, exteriorDifferentialMap_wedge]
  simp_rw [hd]
  rw [AlternatingMap.map_smul_univ, map_prod]

variable (a : ℂ) (hF : A affineF = affineF) (hA : A affineA = C a * affineA)

include hs hX hφ hF hA in
theorem coefficient_character :
    φ (affineNormalSource affineA / normalDensity) =
      algebraMap ℂ K a * (affineNormalSource affineA / normalDensity) := by
  have hd := diagonal_normalDerivative A s hX hs
  have hdF (p : AmbientPoly 4) (h : A p = p) : A (pderiv 0 p) = pderiv 0 p := by rw [hd, h]
  have hdA (p : AmbientPoly 4) (h : A p = C a * p) :
      A (pderiv 0 p) = C a * pderiv 0 p := by rw [hd, h, pderiv_C_mul]
  have h₁ := hdF _ hF
  have h₂ := hdF _ h₁
  have h₃ := hdF _ h₂
  have e₁ := hdA _ hA
  have e₂ := hdA _ e₁
  unfold affineNormalSource normalSourceTwo normalDensity
  simp only [map_inv₀, map_one, map_ofNat, map_mul, map_add, map_sub, map_pow, hφ,
    hA, h₁, h₂, h₃, e₁, e₂, affineMap_constant, div_eq_mul_inv]
  ring

include hs hX hφ hF hA in
theorem invariant_of_character (hdet : a * (∏ j : Fin 4, s j.succ) = 1) :
    exteriorDifferentialMap φ 4 (residueSourceForm affineA) = residueSourceForm affineA := by
  rw [residueSourceForm, map_smulₛₗ]
  change φ (affineNormalSource affineA / normalDensity) • exteriorDifferentialMap φ 4 volume = _
  rw [coefficient_character A s hX hs φ hφ a hF hA, volume_character A s hX φ hφ, smul_smul]
  have hc : algebraMap ℂ K a * algebraMap ℂ K (∏ j : Fin 4, s j.succ) = 1 := by
    rw [← map_mul, hdet, map_one]
  congr 1
  rw [mul_right_comm, hc, one_mul]

end Diagonal

open CycleQ2ProtectedPencilAction

theorem beta_invariant :
    exteriorDifferentialMap beta.toAlgHom 4 (residueSourceForm affineA) = residueSourceForm affineA := by
  apply invariant_of_character (diagonal betaScale) betaScale (diagonal_X _) (by rfl)
    beta.toAlgHom beta_affineMap 1 beta_F
  · simpa only [map_one, one_mul] using beta_A
  · rw [Fin.prod_univ_four]
    change (1 : ℂ) * (-1 * 1 * 1 * -1) = 1
    norm_num

theorem gamma_invariant (z : ℂ) (hz : z ^ 3 = 1) :
    exteriorDifferentialMap (gamma z hz).toAlgHom 4 (residueSourceForm affineA) = residueSourceForm affineA := by
  apply invariant_of_character (diagonal (gammaScale z)) (gammaScale z) (diagonal_X _) (by rfl)
    (gamma z hz).toAlgHom (gamma_affineMap z hz) z (gamma_F z hz) (gamma_A z hz)
  calc
    _ = (z ^ 3) ^ 2 := by simp [Fin.prod_univ_four, gammaScale]; ring
    _ = 1 := by rw [hz, one_pow]

end CycleQ2ProtectedPencilSourceForm
end

#print axioms CycleQ2ProtectedPencilSourceForm.invariant_of_character
#print axioms CycleQ2ProtectedPencilSourceForm.beta_invariant
#print axioms CycleQ2ProtectedPencilSourceForm.gamma_invariant
