import Proposal.GeometricHodgeCyclicResidue
import Proposal.GeometricHodgeEulerLocalizedGradient

/-!
# Equivariant lifts for the normal connecting cocycle

On a normalized coordinate chart the ambient gradient is a four-component
linear form. On any open where one partial is invertible a deformation has a
unique lift supported in that coordinate. The diagonal substitution preserves
this normalization. Differences of two such lifts therefore carry the
character of the original polynomial deformation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeCyclicNormalLifts

open MvPolynomial CycleQ2HodgeCyclicAction CycleQ2HodgeEuler
  CycleQ2HodgeEulerContractionCharts CycleQ2GeometricIncidenceProj CycleQ2GenericSexticGradient

variable (φ : CoeffRing →+* ℂ) (i : Fin 4)
variable {S : Type} [CommRing S] [Algebra ℂ S]
variable (f : chart φ i →ₐ[ℂ] S) (z : ℂ) (hz : z^3=1) (g : S →ₐ[ℂ] S)
  (hf : ∀ x, g (f x) = f (chartAction φ z hz i x))

def gradientCoefficient (j : Fin 4) : S := f (gradientEntry (F φ i) j)

def normal (v : Fin 4 → S) : S := ∑ a, gradientCoefficient φ i f a * v a

def velocity (v : Fin 4 → S) (a : Fin 4) : S :=
  algebraMap ℂ S (chartFactor z i a)⁻¹ * g (v a)

include hf in
theorem partial_action (a : Fin 4) :
    g (gradientCoefficient φ i f a) = algebraMap ℂ S (chartFactor z i a)⁻¹ * gradientCoefficient φ i f a := by
  rw [gradientCoefficient, hf, chartAction_gradient, map_mul, AlgHom.commutes]

include hf in
theorem normal_velocity (v : Fin 4 → S) :
    normal φ i f (velocity i z g v) = g (normal φ i f v) := by
  rw [normal, normal, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, partial_action φ i f z hz g hf, velocity]
  ring

def lift (j : Fin 4) (hj : IsUnit (gradientCoefficient φ i f j)) (t : S) (a : Fin 4) : S :=
  if a = j then (↑hj.unit⁻¹ : S) * t else 0

theorem lift_solve (j : Fin 4) (hj : IsUnit (gradientCoefficient φ i f j)) (t : S) :
    normal φ i f (lift φ i f j hj t) = t := by
  rw [normal, Finset.sum_eq_single j]
  · rw [lift, if_pos rfl, ← mul_assoc]
    simpa only [← hj.unit_spec, Units.mul_inv, one_mul]
  · intro b _ hb
    rw [lift, if_neg hb, mul_zero]
  · simp

private theorem lift_unique (j : Fin 4) (hj : IsUnit (gradientCoefficient φ i f j)) (t : S)
    (v : Fin 4 → S) (hv : ∀ a, a ≠ j → v a = 0) (h : normal φ i f v = t) :
    v = lift φ i f j hj t := by
  funext a
  by_cases ha : a = j
  · subst a
    apply hj.mul_left_cancel
    rw [lift, if_pos rfl, ← mul_assoc]
    have hi : gradientCoefficient φ i f j * (↑hj.unit⁻¹ : S) = 1 := by rw [← hj.unit_spec, Units.mul_inv]
    rw [hi, one_mul]
    rw [normal, Finset.sum_eq_single j] at h
    · exact h
    · intro b _ hb
      rw [hv b hb, mul_zero]
    · simp
  · rw [hv a ha, lift, if_neg ha]

include hf in
theorem velocity_lift (j : Fin 4) (hj : IsUnit (gradientCoefficient φ i f j)) (t : S) :
    velocity i z g (lift φ i f j hj t) = lift φ i f j hj (g t) := by
  apply lift_unique
  · intro a ha
    rw [velocity, lift, if_neg ha, map_zero, mul_zero]
  · rw [normal_velocity φ i f z hz g hf, lift_solve]

include hf in
theorem polynomial_lift_difference (j k : Fin 4) (hj : IsUnit (gradientCoefficient φ i f j))
    (hk : IsUnit (gradientCoefficient φ i f k)) (χ : ZMod 3) (p : MvPolynomial (Fin 5) ℂ)
    (hp : CycleQ2IncidenceEquations.HG p (6,χ)) :
    let t := f (chartMap φ i (dehom i p))
    let v := lift φ i f j hj t - lift φ i f k hk t
    normal φ i f v = 0 ∧ velocity i z g v = algebraMap ℂ S (z^χ.val) • v := by
  dsimp only
  let t := f (chartMap φ i (dehom i p))
  have ht : g t = algebraMap ℂ S (z^χ.val) * t := by
    rw [show g t = f (chartAction φ z hz i (chartMap φ i (dehom i p))) from hf _]
    change f (chartMap φ i (chartPoly z i (dehom i p))) = _
    rw [chartPoly_direction z hz i χ p hp, map_mul, map_mul]
    change f (algebraMap ℂ (chart φ i) (z^χ.val)) * t = _
    rw [AlgHom.commutes]
  have hom (a : Fin 4) (ha : IsUnit (gradientCoefficient φ i f a)) :
      lift φ i f a ha (g t) = algebraMap ℂ S (z^χ.val) • lift φ i f a ha t := by
    funext b
    by_cases hb : b=a <;> simp [lift, ht, hb, mul_left_comm, mul_assoc]
  constructor
  · unfold normal
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    change normal φ i f (lift φ i f j hj t) - normal φ i f (lift φ i f k hk t) = 0
    rw [lift_solve, lift_solve, sub_self]
  · have h (v w : Fin 4 → S) : velocity i z g (v-w) = velocity i z g v - velocity i z g w := by
      funext a
      simp only [velocity, Pi.sub_apply, map_sub, mul_sub]
    rw [h, velocity_lift φ i f z hz g hf, velocity_lift φ i f z hz g hf, hom, hom, smul_sub]

section LocalizedTangent
variable (M : Submonoid (chart φ i)) [Algebra (chart φ i) S] [IsScalarTower ℂ (chart φ i) S] [IsLocalization M S]

private abbrev base : chart φ i →ₐ[ℂ] S := IsScalarTower.toAlgHom ℂ (chart φ i) S

variable (e : S ≃ₐ[ℂ] S) (he : ∀ x, e (base φ i (S := S) x) = base φ i (chartAction φ z hz i x))

include he in
theorem tangentVelocity (D : Derivation ℂ S S) :
    let E := CycleQ2HodgeEulerLocalizedGradient.derivationEquiv (F φ i) M S
    (E (conjugate e D)).val = velocity i z e.toAlgHom (E D).val := by
  funext a
  let y := base φ i (S := S) (chartMap φ i (X a))
  let d := chartFactor z i a
  have hy : e y = algebraMap ℂ S d * y := by
    rw [show e y = base φ i (chartAction φ z hz i (chartMap φ i (X a))) from he _]
    change base φ i (chartMap φ i (chartPoly z i (X a))) = _
    rw [chartPoly_X, map_mul, map_mul]
    change base φ i (algebraMap ℂ (chart φ i) d) * y = _
    rw [AlgHom.commutes]
  have hi : e.symm y = algebraMap ℂ S d⁻¹ * y := by
    apply e.injective
    rw [e.apply_symm_apply, map_mul, AlgEquiv.commutes, hy, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ (chartFactor_ne_zero z hz i a), map_one, one_mul]
  change e (D (e.symm y)) = algebraMap ℂ S d⁻¹ * e (D y)
  rw [hi, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
    smul_eq_mul, map_mul, AlgEquiv.commutes]

include he in
theorem polynomial_tangent (j k : Fin 4) (hj : IsUnit (gradientCoefficient φ i (base φ i (S := S)) j))
    (hk : IsUnit (gradientCoefficient φ i (base φ i (S := S)) k)) (χ : ZMod 3)
    (p : MvPolynomial (Fin 5) ℂ) (hp : CycleQ2IncidenceEquations.HG p (6,χ)) :
    let f := base φ i (S := S)
    let t := f (chartMap φ i (dehom i p))
    ∃ D : Derivation ℂ S S,
      (CycleQ2HodgeEulerLocalizedGradient.derivationEquiv (F φ i) M S D).val =
        lift φ i f j hj t - lift φ i f k hk t ∧
      conjugate e D = algebraMap ℂ S (z^χ.val) • D := by
  dsimp only
  let f := base φ i (S := S)
  let t := f (chartMap φ i (dehom i p))
  let v := lift φ i f j hj t - lift φ i f k hk t
  obtain ⟨hzero,heigen⟩ := polynomial_lift_difference φ i f z hz e.toAlgHom he j k hj hk χ p hp
  let E := CycleQ2HodgeEulerLocalizedGradient.derivationEquiv (F φ i) M S
  let u : (pairing (CycleQ2HodgeEulerLocalizedGradient.gradientRow (F φ i) S)).ker :=
    ⟨v, by rw [LinearMap.mem_ker, pairing_apply]; exact hzero⟩
  let D := E.symm u
  have hD : (E D).val = v := congrArg Subtype.val (E.apply_symm_apply u)
  refine ⟨D, hD, E.injective (Subtype.ext ?_)⟩
  change (E (conjugate e D)).val = (E (algebraMap ℂ S (z^χ.val) • D)).val
  rw [map_smul]
  change (E (conjugate e D)).val = algebraMap ℂ S (z^χ.val) • (E D).val
  rw [tangentVelocity φ i z hz M e he D, hD]
  exact heigen

end LocalizedTangent

end CycleQ2HodgeCyclicNormalLifts
end

#print axioms CycleQ2HodgeCyclicNormalLifts.polynomial_lift_difference

#print axioms CycleQ2HodgeCyclicNormalLifts.polynomial_tangent
