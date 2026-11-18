import Proposal.GeometricTarget01Part01
import Proposal.GeometricAffineOverlap

/-! The paired-sign and cubic-root symmetries on the protected function field
in the chart X₀ = 1. These formulas include the rescaling of X₀ in the
projective cubic-root action.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ProtectedPencilAction

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface CycleQ2AffineDifferentials CycleQ2GeometricAffineOverlap

private abbrev P := AmbientPoly 4

def betaScale : Fin 5 → ℂ := ![1,-1,1,1,-1]
def gammaScale (z : ℂ) : Fin 5 → ℂ := ![1,z,z^2,z,z]

private theorem chart_vector (v : Fin 5 → ℂ) : Fin.cases 1 v = ![1,v 0,v 1,v 2,v 3,v 4] := by
  funext i
  fin_cases i <;> rfl

theorem beta_chart (v : Fin 5 → ℂ) (i : Fin 5) :
    CycleQ2GeometricTarget.beta (Fin.cases 1 v) i.succ = betaScale i * v i := by
  fin_cases i <;> simp [CycleQ2GeometricTarget.beta, betaScale, chart_vector]

theorem gamma_chart (z : ℂ) (hz : z^3 = 1) (v : Fin 5 → ℂ) (i : Fin 5) :
    CycleQ2GeometricTarget.gamma z (Fin.cases 1 v) i.succ =
      z^2 * (gammaScale z i * v i) := by
  have h4 : z^4 = z := by rw [show (4 : ℕ) = 3+1 by decide, pow_succ, hz, one_mul]
  fin_cases i <;> simp [CycleQ2GeometricTarget.gamma, gammaScale, chart_vector] <;>
    ring_nf <;> simp [hz,h4]

def diagonal (s : Fin 5 → ℂ) : P →ₐ[ℂ] P := aeval (fun i => C (s i) * X i)

theorem diagonal_X (s : Fin 5 → ℂ) (i : Fin 5) : diagonal s (X i) = C (s i) * X i := aeval_X _ _
theorem diagonal_C (s : Fin 5 → ℂ) (a : ℂ) : diagonal s (C a) = C a := aeval_C _ _

theorem beta_F : diagonal betaScale affineF = affineF := by
  rw [affineF_formula]
  simp [diagonal_X, betaScale]
  ring

theorem beta_A : diagonal betaScale affineA = affineA := by
  rw [CycleQ2AffineWeightedTransfer.affineA_formula]
  simp [diagonal_X, betaScale]
  ring

private theorem scalar_pow {R : Type*} [Monoid R] {z : R} (hz : z^3 = 1) (n : ℕ) :
    z^n = z^(n%3) := by
  calc
    _ = z^(n%3 + 3*(n/3)) := congrArg (z^·) (Nat.mod_add_div n 3).symm
    _ = _ := by rw [pow_add, pow_mul, hz, one_pow, mul_one]

private theorem C_cube (z : ℂ) (hz : z^3 = 1) : (C z : P)^3 = 1 := by
  rw [← map_pow, hz, map_one]

theorem gamma_F (z : ℂ) (hz : z^3 = 1) : diagonal (gammaScale z) affineF = affineF := by
  rw [affineF_formula]
  simp [diagonal_X, gammaScale, mul_pow]
  ring_nf
  simp only [scalar_pow (C_cube z hz) 3, scalar_pow (C_cube z hz) 6,
    scalar_pow (C_cube z hz) 12]
  norm_num
  ring

theorem gamma_A (z : ℂ) (hz : z^3 = 1) :
    diagonal (gammaScale z) affineA = C z * affineA := by
  rw [CycleQ2AffineWeightedTransfer.affineA_formula]
  simp [diagonal_X, gammaScale, mul_pow]
  ring_nf
  rw [scalar_pow (C_cube z hz) 10]
  norm_num

private theorem diagonal_inverse (s t : Fin 5 → ℂ) (h : ∀ i, t i * s i = 1) :
    (diagonal s).comp (diagonal t) = AlgHom.id ℂ P := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, diagonal_X, map_mul, diagonal_C, AlgHom.id_apply]
  rw [← mul_assoc, ← map_mul, h i, map_one, one_mul]

private def polynomialEquiv (s t : Fin 5 → ℂ) (h : ∀ i, t i * s i = 1) : P ≃ₐ[ℂ] P :=
  AlgEquiv.ofAlgHom (diagonal s) (diagonal t) (diagonal_inverse s t h)
    (diagonal_inverse t s (fun i => (mul_comm _ _).trans (h i)))

private def coordinateEquiv (s t : Fin 5 → ℂ) (h : ∀ i, t i * s i = 1)
    (hF : diagonal s affineF = affineF) : AffineCoordinateRing ≃ₐ[ℂ] AffineCoordinateRing :=
  Ideal.quotientEquivAlg _ _ (polynomialEquiv s t h) (by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p : P => Ideal.span ({p} : Set P)) hF.symm)

private def fieldEquiv (s t : Fin 5 → ℂ) (h : ∀ i, t i * s i = 1)
    (hF : diagonal s affineF = affineF) : K ≃ₐ[ℂ] K :=
  IsFractionRing.algEquivOfAlgEquiv (coordinateEquiv s t h hF)

private theorem fieldEquiv_affineMap (s t : Fin 5 → ℂ) (h : ∀ i, t i * s i = 1)
    (hF : diagonal s affineF = affineF) (p : P) :
    fieldEquiv s t h hF (affineMap p) = affineMap (diagonal s p) := by
  change IsFractionRing.algEquivOfAlgEquiv (coordinateEquiv s t h hF)
    (algebraMap AffineCoordinateRing K (affineProjection p)) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

def beta : K ≃ₐ[ℂ] K := fieldEquiv betaScale betaScale (by
  intro i
  fin_cases i <;> norm_num [betaScale]) beta_F

def gamma (z : ℂ) (hz : z^3 = 1) : K ≃ₐ[ℂ] K :=
  fieldEquiv (gammaScale z) (gammaScale (z^2)) (by
    intro i
    fin_cases i <;> simp [gammaScale] <;> ring_nf <;>
      first | exact hz | simpa only [scalar_pow hz 6] using (pow_zero z))
    (gamma_F z hz)

theorem beta_affineMap (p : P) : beta (affineMap p) = affineMap (diagonal betaScale p) :=
  fieldEquiv_affineMap _ _ _ _ _

theorem gamma_affineMap (z : ℂ) (hz : z^3 = 1) (p : P) :
    gamma z hz (affineMap p) = affineMap (diagonal (gammaScale z) p) :=
  fieldEquiv_affineMap _ _ _ _ _

private theorem field_hom_ext {f g : K →+* K}
    (h : ∀ p : P, f (affineMap p) = g (affineMap p)) : f = g := by
  apply IsFractionRing.ringHom_ext (A := AffineCoordinateRing)
  intro x
  obtain ⟨p,rfl⟩ := affineProjection_surjective x
  exact h p

theorem beta_involutive : Function.Involutive beta := by
  have h : beta.toRingHom.comp beta.toRingHom = RingHom.id K := by
    apply field_hom_ext
    intro p
    change beta (beta (affineMap p)) = affineMap p
    rw [beta_affineMap, beta_affineMap]
    exact congrArg affineMap (AlgHom.congr_fun (diagonal_inverse betaScale betaScale
      (fun i => by fin_cases i <;> norm_num [betaScale])) p)
  exact RingHom.congr_fun h

theorem gamma_cube (z : ℂ) (hz : z^3 = 1) (x : K) : gamma z hz (gamma z hz (gamma z hz x)) = x := by
  let f := diagonal (gammaScale z)
  have hs (i : Fin 5) : gammaScale z i ^ 3 = 1 := by
    fin_cases i <;> simp [gammaScale, hz, ← pow_mul, scalar_pow hz 6]
  have he : f.comp (f.comp f) = AlgHom.id ℂ P := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [f, AlgHom.comp_apply, diagonal_X, diagonal_C, map_mul, AlgHom.id_apply]
    have hc : (C (gammaScale z i) : P)^3 = 1 := by rw [← map_pow, hs, map_one]
    linear_combination X i * hc
  let g := (gamma z hz).toRingHom
  have h : g.comp (g.comp g) = RingHom.id K := by
    apply field_hom_ext
    intro p
    change gamma z hz (gamma z hz (gamma z hz (affineMap p))) = _
    rw [gamma_affineMap, gamma_affineMap, gamma_affineMap]
    exact congrArg affineMap (AlgHom.congr_fun he p)
  exact RingHom.congr_fun h x

theorem beta_gamma_commute (z : ℂ) (hz : z^3 = 1) : Function.Commute beta (gamma z hz) := by
  have he : (diagonal betaScale).comp (diagonal (gammaScale z)) =
      (diagonal (gammaScale z)).comp (diagonal betaScale) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, diagonal_X, diagonal_C, map_mul]
    ring
  have h : beta.toRingHom.comp (gamma z hz).toRingHom = (gamma z hz).toRingHom.comp beta.toRingHom := by
    apply field_hom_ext
    intro p
    change beta (gamma z hz (affineMap p)) = gamma z hz (beta (affineMap p))
    rw [gamma_affineMap, beta_affineMap, beta_affineMap, gamma_affineMap]
    exact congrArg affineMap (AlgHom.congr_fun he p)
  exact RingHom.congr_fun h

theorem beta_coordinate (i : Fin 5) :
    beta (CycleQ2AffineWeightedTransfer.z i) =
      algebraMap ℂ K (betaScale i) * CycleQ2AffineWeightedTransfer.z i := by
  rw [CycleQ2AffineWeightedTransfer.z, beta_affineMap, diagonal_X, map_mul, affineMap_constant]

theorem gamma_coordinate (z : ℂ) (hz : z^3 = 1) (i : Fin 5) :
    gamma z hz (CycleQ2AffineWeightedTransfer.z i) =
      algebraMap ℂ K (gammaScale z i) * CycleQ2AffineWeightedTransfer.z i := by
  rw [CycleQ2AffineWeightedTransfer.z, gamma_affineMap, diagonal_X, map_mul, affineMap_constant]

open CycleQ2AffineWeightedTransfer in
theorem beta_parameter : beta parameter = parameter := by
  simp [parameter, u, v, beta_coordinate, betaScale]

open CycleQ2AffineWeightedTransfer in
theorem gamma_parameter (ζ : ℂ) (hζ : ζ^3 = 1) : gamma ζ hζ parameter = parameter := by
  have h0 : ζ ≠ 0 := by rintro rfl; norm_num at hζ
  have hu : algebraMap ℂ AffineFunctionField ζ ≠ 0 := (map_ne_zero (algebraMap ℂ AffineFunctionField)).mpr h0
  simp only [parameter, u, v, map_div₀, gamma_coordinate]
  exact mul_div_mul_left _ _ hu

private theorem coordinateDifferential_action (f : K ≃ₐ[ℂ] K) (s : Fin 5 → ℂ)
    (hf : ∀ p, f (affineMap p) = affineMap (diagonal s p)) (j : Fin 4) :
    differentialMap f.toAlgHom (coordinateDifferential j) =
      algebraMap ℂ K (s j.succ) • coordinateDifferential j := by
  change differentialMap f.toAlgHom (KaehlerDifferential.D ℂ K (affineMap (X j.succ))) = _
  rw [differentialMap_D]
  change KaehlerDifferential.D ℂ K (f (affineMap (X j.succ))) = _
  rw [hf, diagonal_X,
    map_mul, affineMap_constant, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  rfl

theorem beta_coordinateDifferential (j : Fin 4) :
    differentialMap beta.toAlgHom (coordinateDifferential j) =
      algebraMap ℂ K (betaScale j.succ) • coordinateDifferential j :=
  coordinateDifferential_action _ _ beta_affineMap j

theorem gamma_coordinateDifferential (z : ℂ) (hz : z^3 = 1) (j : Fin 4) :
    differentialMap (gamma z hz).toAlgHom (coordinateDifferential j) =
      algebraMap ℂ K (gammaScale z j.succ) • coordinateDifferential j :=
  coordinateDifferential_action _ _ (gamma_affineMap z hz) j

end CycleQ2ProtectedPencilAction
end

#print axioms CycleQ2ProtectedPencilAction.beta_coordinateDifferential
#print axioms CycleQ2ProtectedPencilAction.gamma_coordinateDifferential
#print axioms CycleQ2ProtectedPencilAction.gamma_A
#print axioms CycleQ2ProtectedPencilAction.beta_gamma_commute
#print axioms CycleQ2ProtectedPencilAction.gamma_parameter
