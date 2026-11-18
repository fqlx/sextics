import Proposal.GeometricHodgeEulerSequence
import Proposal.GeometricIncidenceDehomogenizedChart
import Proposal.SolutionSupport07Part01

/-!
# Tangent-coordinate transitions on overlaps of weighted sextic charts

On the overlap of the weight-one charts at i and k, divide the coordinate
of weight w by the w-th power of the k-coordinate of the first chart.
Differentiation in the actual localization gives the weighted quotient rule,
including the radial correction for the weight-two coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeEuler

open MvPolynomial CycleQ2GenericSexticGradient CycleQ2GeometricIncidenceProj

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i k : Fin 4)

abbrev overlap := Localization.Away (coordinate φ i k.castSucc)

def localCoordinate (j : Fin 5) : overlap φ i k :=
  algebraMap (chart φ i) _ (coordinate φ i j)

def invPivot : overlap φ i k := IsLocalization.Away.invSelf (coordinate φ i k.castSucc)

@[simp] theorem localCoordinate_mul_invPivot : localCoordinate φ i k k.castSucc * invPivot φ i k = 1 :=
  IsLocalization.Away.mul_invSelf _

def ratioCoordinate (j : Fin 5) : overlap φ i k :=
  invPivot φ i k ^ geometricWeight j * localCoordinate φ i k j

private theorem weight_linear (j : Fin 4) : geometricWeight j.castSucc = 1 := by fin_cases j <;> rfl

@[simp] theorem ratioCoordinate_pivot : ratioCoordinate φ i k k.castSucc = 1 := by
  rw [ratioCoordinate, weight_linear, pow_one, mul_comm, localCoordinate_mul_invPivot]

private def evaluateNew : MvPolynomial (Fin 4) R →ₐ[R] overlap φ i k :=
  aeval (fun a => ratioCoordinate φ i k (k.castSucc.succAbove a))

private theorem evaluateNew_comp :
    (evaluateNew φ i k).comp (dehom (R := R) k) = aeval (ratioCoordinate φ i k) := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.succAboveCases k.castSucc ?_ (fun a => ?_) j
  · simp
  · simp [evaluateNew]

private theorem oldPoint_equation :
    aeval (localCoordinate φ i k) (MvPolynomial.map φ universalF) = 0 := by
  let a := IsScalarTower.toAlgHom R (chart φ i) (overlap φ i k)
  have h : aeval (localCoordinate φ i k) = (a.comp (chartMap φ i)).comp (dehom i) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [aeval_X]
    rfl
  rw [h]
  change a (chartMap φ i (F φ i)) = 0
  rw [chartMap_F, map_zero]

private theorem evaluateNew_equation : evaluateNew φ i k (F φ k) = 0 := by
  let _ : Algebra ℂ R := (φ.comp (C : ℂ →+* CoeffRing)).toAlgebra
  have h := AlgHom.congr_fun (evaluateNew_comp φ i k) (MvPolynomial.map φ universalF)
  change evaluateNew φ i k (F φ k) = aeval (ratioCoordinate φ i k) (MvPolynomial.map φ universalF) at h
  rw [h]
  have hs := CycleQ2IncidenceDehomogenizedChart.weighted_homogeneous_eval_scale
    (algebraMap R (overlap φ i k)) (localCoordinate φ i k) (invPivot φ i k)
    (MvPolynomial.map φ universalF) 6 (family_homogeneous φ)
  change aeval (ratioCoordinate φ i k) (MvPolynomial.map φ universalF) =
    invPivot φ i k ^ 6 * aeval (localCoordinate φ i k) (MvPolynomial.map φ universalF) at hs
  rw [hs, oldPoint_equation, mul_zero]

/-- The restriction of the second chart's coordinate ring to the actual principal overlap. -/
def overlapMap : chart φ k →ₐ[R] overlap φ i k :=
  Ideal.Quotient.liftₐ _ (evaluateNew φ i k) (fun _ hp =>
    (Ideal.span_singleton_le_iff_mem (RingHom.ker (evaluateNew φ i k).toRingHom)).mpr
      (evaluateNew_equation φ i k) hp)

theorem overlapMap_coordinate (j : Fin 5) :
    overlapMap φ i k (coordinate φ k j) = ratioCoordinate φ i k j := by
  change evaluateNew φ i k (dehom k (X j)) = _
  simpa only [AlgHom.comp_apply, aeval_X] using
    AlgHom.congr_fun (evaluateNew_comp φ i k) (X j)

@[simp] theorem ratioCoordinate_oldPivot : ratioCoordinate φ i k i.castSucc = invPivot φ i k := by
  simp [ratioCoordinate, localCoordinate, coordinate]

theorem invPivot_isUnit : IsUnit (invPivot φ i k) :=
  isUnit_iff_exists_inv.mpr ⟨localCoordinate φ i k k.castSucc,
    (mul_comm _ _).trans (localCoordinate_mul_invPivot φ i k)⟩

/-- Pullback to the overlap, with the second chart's inverse coordinate included. -/
def transition : overlap φ k i →ₐ[R] overlap φ i k :=
  IsLocalization.Away.liftAlgHom (coordinate φ k i.castSucc) (f := overlapMap φ i k)
    (by rw [overlapMap_coordinate, ratioCoordinate_oldPivot]; exact invPivot_isUnit φ i k)

theorem transition_localCoordinate (j : Fin 5) :
    transition φ i k (localCoordinate φ k i j) = ratioCoordinate φ i k j :=
  (IsLocalization.lift_eq _ (coordinate φ k j)).trans (overlapMap_coordinate φ i k j)

theorem transition_invPivot : transition φ i k (invPivot φ k i) = localCoordinate φ i k k.castSucc := by
  apply (invPivot_isUnit φ i k).mul_left_cancel
  have h := congrArg (transition φ i k) (localCoordinate_mul_invPivot φ k i)
  rw [map_mul, map_one, transition_localCoordinate, ratioCoordinate_oldPivot] at h
  exact h.trans ((mul_comm _ _).trans (localCoordinate_mul_invPivot φ i k)).symm

theorem transition_ratioCoordinate (j : Fin 5) :
    transition φ i k (ratioCoordinate φ k i j) = localCoordinate φ i k j := by
  rw [ratioCoordinate, map_mul, map_pow, transition_invPivot, transition_localCoordinate,
    ratioCoordinate, ← mul_assoc, ← mul_pow, localCoordinate_mul_invPivot, one_pow, one_mul]

theorem transition_comp : (transition φ i k).comp (transition φ k i) = AlgHom.id R (overlap φ i k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coordinate φ i k.castSucc))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  have h := transition_ratioCoordinate φ i k (i.castSucc.succAbove j)
  rw [← transition_localCoordinate φ k i] at h
  change transition φ i k (transition φ k i (algebraMap (chart φ i) (overlap φ i k)
    (chartMap φ i (X j)))) = algebraMap (chart φ i) (overlap φ i k) (chartMap φ i (X j))
  simpa only [localCoordinate, coordinate, dehom_X_succAbove] using h

/-- The two presentations of the principal overlap are isomorphic by the weighted coordinate change. -/
def overlapEquiv : overlap φ k i ≃ₐ[R] overlap φ i k :=
  AlgEquiv.ofAlgHom (transition φ i k) (transition φ k i)
    (transition_comp φ i k) (transition_comp φ k i)

private theorem weighted_quotient_rule {B : Type*} [CommRing B] [Algebra R B]
    (D : Derivation R B B) (u v x : B) (hu : u*v = 1) (w : ℕ) (hw : w=1 ∨ w=2) :
    D (u^w * x) = u^w * (D x - (w:B) * u * x * D v) := by
  have h := D.leibniz_of_mul_eq_one hu
  rw [smul_eq_mul] at h
  rcases hw with rfl | rfl
  · simp only [pow_one, Nat.cast_one, one_mul, Derivation.leibniz, smul_eq_mul, h]
    ring
  · simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      Nat.cast_ofNat, h]
    norm_num
    ring

/-- Intrinsic derivative of the coordinate from chart k, computed in chart i on their overlap. -/
theorem overlap_derivative (D : Derivation R (chart φ i) (chart φ i)) (j : Fin 5) :
    CycleQ2LocalizationDerivation.extend (S := overlap φ i k)
      (Submonoid.powers (coordinate φ i k.castSucc)) D (overlapMap φ i k (coordinate φ k j)) =
      invPivot φ i k ^ geometricWeight j *
        (algebraMap (chart φ i) _ (D (coordinate φ i j)) -
          (geometricWeight j : overlap φ i k) * invPivot φ i k * localCoordinate φ i k j *
            algebraMap (chart φ i) _ (D (coordinate φ i k.castSucc))) := by
  let δ := CycleQ2LocalizationDerivation.extend (S := overlap φ i k)
    (Submonoid.powers (coordinate φ i k.castSucc)) D
  have h (a : Fin 5) : δ (localCoordinate φ i k a) =
      algebraMap (chart φ i) (overlap φ i k) (D (coordinate φ i a)) :=
    CycleQ2LocalizationDerivation.extend_map _ D _
  have hw : geometricWeight j = 1 ∨ geometricWeight j = 2 := by fin_cases j <;> decide
  rw [overlapMap_coordinate, ratioCoordinate]
  exact (weighted_quotient_rule δ _ _ _ ((mul_comm _ _).trans (localCoordinate_mul_invPivot φ i k))
    _ hw).trans (by rw [h, h])

/-- The derivation represented by the ambient tangent tuple on every normalized homogeneous
coordinate, including the coordinate set equal to one. -/
theorem tangentQuotientEquiv_coordinate_all (v : RawTangent φ i) (j : Fin 5) :
    tangentQuotientEquiv φ i (Submodule.Quotient.mk v) (coordinate φ i j) =
      v.val j - v.val i.castSucc * radial φ i j := by
  refine Fin.succAboveCases i.castSucc ?_ (fun a => ?_) j
  · simp [coordinate, Derivation.map_one_eq_zero]
  · rw [coordinate, dehom_X_succAbove, tangentQuotientEquiv_coordinate]

private theorem cancel_radial {A : Type*} [CommRing A] (u t n x v j k : A) (h : t*u=1) :
    (j - v * (n*x)) - n*u*x * (k - v*t) = j - n*u*x*k := by
  calc
    _ = (j - n*u*x*k) + n*x*v*(t*u - 1) := by ring
    _ = _ := by rw [h]; ring

/-- The intrinsic derivation's transition formula in terms of any five-tuple representative
in the tangent kernel. Its original radial contribution cancels on the overlap. -/
theorem rawTangent_overlap (v : RawTangent φ i) (j : Fin 5) :
    CycleQ2LocalizationDerivation.extend (S := overlap φ i k)
      (Submonoid.powers (coordinate φ i k.castSucc))
      (tangentQuotientEquiv φ i (Submodule.Quotient.mk v))
      (overlapMap φ i k (coordinate φ k j)) =
        invPivot φ i k ^ geometricWeight j *
          (algebraMap (chart φ i) (overlap φ i k) (v.val j) -
            (geometricWeight j : overlap φ i k) * invPivot φ i k * localCoordinate φ i k j *
              algebraMap (chart φ i) (overlap φ i k) (v.val k.castSucc)) := by
  rw [overlap_derivative, tangentQuotientEquiv_coordinate_all, tangentQuotientEquiv_coordinate_all]
  have hr (a : Fin 5) : algebraMap (chart φ i) (overlap φ i k) (radial φ i a) =
      (geometricWeight a : overlap φ i k) * localCoordinate φ i k a := by
    simp only [radial, localCoordinate, map_mul, map_natCast]
  simp only [map_sub, map_mul, hr, weight_linear, Nat.cast_one, one_mul]
  congr 1
  exact cancel_radial _ _ _ _ _ _ _ (localCoordinate_mul_invPivot φ i k)

end CycleQ2HodgeEuler
end

#print axioms CycleQ2HodgeEuler.overlapMap_coordinate
#print axioms CycleQ2HodgeEuler.overlap_derivative

#print axioms CycleQ2HodgeEuler.overlapEquiv

#print axioms CycleQ2HodgeEuler.rawTangent_overlap
