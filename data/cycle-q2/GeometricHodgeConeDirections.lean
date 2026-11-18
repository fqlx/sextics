import Proposal.GeometricHodgeInfinitesimalQuotient
import Proposal.GeometricHodgeThreefold

/-!
# Deformation directions on the actual graded cone

The projective normal sections lie in the coordinate ring modulo F.
Euler's identity and invertibility of six show that F already vanishes
in the Jacobian quotient. In each character, the actual degree-six
cone piece modulo the five partials times coordinate velocities is
canonically the corresponding Jacobian piece.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeConeDirections

open MvPolynomial CycleQ2HodgeInfinitesimalQuotient CycleQ2HiggsJacobianFrames
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricIncidenceProj CycleQ2IncidenceNormalForm
open CycleQ2GenericSexticGradient (CoeffRing)

variable {K : Type} [CommRing K] (φ : CoeffRing →+* K)

theorem equation_jacobian_zero : quotientMap φ (equation φ) = 0 := by
  let c : ℂ →+* QuotientRing φ := (algebraMap K _).comp (φ.comp (algebraMap ℂ _))
  have hu : IsUnit (6 : QuotientRing φ) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (6 : ℂ) ≠ 0)).map c
  have hj (j : Fin 5) : quotientMap φ (pderiv j (equation φ)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
  have h := congrArg (quotientMap φ) (equation_homogeneous φ).sum_weight_X_mul_pderiv
  simp only [map_sum, map_nsmul, map_mul, hj, mul_zero, nsmul_zero, Finset.sum_const_zero] at h
  apply hu.mul_left_cancel
  simpa only [mul_zero, nsmul_eq_mul, Nat.cast_ofNat] using h.symm

def coneToJacobian : cone φ →ₐ[K] QuotientRing φ :=
  Ideal.Quotient.liftₐ _ (quotientMap φ) (by
    have h : Ideal.span {equation φ} ≤ RingHom.ker (quotientMap φ).toRingHom :=
      Ideal.span_le.mpr (by rintro _ (rfl : _ = equation φ); exact equation_jacobian_zero φ)
    exact fun _ ha => h ha)

def piece (n : ℕ) (χ : ZMod 3) : Submodule K (cone φ) :=
  (weightedHomogeneousSubmodule K fullGrading (n,χ)).map
    (Ideal.Quotient.mkₐ K (Ideal.span {equation φ})).toLinearMap

abbrev Vels (χ : ZMod 3) := (i : Fin 5) → piece φ (fullGrading i).1 (χ + (fullGrading i).2)

def sectionClass {n : ℕ} {χ : ZMod 3} (p : weightedHomogeneousSubmodule K fullGrading (n,χ)) : piece φ n χ :=
  ⟨quotient φ p, p, p.property, rfl⟩

def velocityClass {χ : ZMod 3} (v : Velocities K χ) : Vels φ χ := fun i => sectionClass φ (v i)

theorem velocityClass_surjective {χ : ZMod 3} : Function.Surjective (velocityClass φ (χ := χ)) := by
  intro w
  have h (i : Fin 5) : ∃ p : weightedHomogeneousSubmodule K fullGrading ((fullGrading i).1,χ+(fullGrading i).2),
      sectionClass φ p = w i := by
    obtain ⟨p,hp,he⟩ := (w i).property
    exact ⟨⟨p,hp⟩, Subtype.ext he⟩
  exact ⟨fun i => (h i).choose, funext fun i => (h i).choose_spec⟩

def normalValue {χ : ZMod 3} (w : Vels φ χ) : cone φ :=
  ∑ j, (w j : cone φ) * quotient φ (pderiv j (equation φ))

theorem normalValue_velocityClass {χ : ZMod 3} (v : Velocities K χ) :
    normalValue φ (velocityClass φ v) = quotient φ (velocityDerivation v (equation φ)) := by
  rw [velocityDerivation_apply, map_sum]
  simp only [map_mul]
  rfl

def normal (χ : ZMod 3) : Vels φ χ →ₗ[K] piece φ 6 χ where
  toFun w := ⟨normalValue φ w, by
    obtain ⟨v,rfl⟩ := velocityClass_surjective φ w
    exact ⟨_, velocity_homogeneous φ v, (normalValue_velocityClass φ v).symm⟩⟩
  map_add' v w := Subtype.ext (by simp [normalValue, add_mul, Finset.sum_add_distrib])
  map_smul' c v := Subtype.ext (by simp [normalValue, Finset.smul_sum, smul_mul_assoc])

theorem normal_velocityClass {χ : ZMod 3} (v : Velocities K χ) :
    normal φ χ (velocityClass φ v) = sectionClass φ (derivative φ χ v) :=
  Subtype.ext (normalValue_velocityClass φ v)

def toJacobian (n : ℕ) (χ : ZMod 3) : piece φ n χ →ₗ[K] gradedPiece φ n χ :=
  (((coneToJacobian φ).toLinearMap.comp (piece φ n χ).subtype).codRestrict _ (by
    rintro ⟨_,p,hp,rfl⟩
    exact ⟨p,hp,rfl⟩))

theorem toJacobian_surjective (n : ℕ) (χ : ZMod 3) : Function.Surjective (toJacobian φ n χ) := by
  rintro ⟨_,p,hp,rfl⟩
  exact ⟨sectionClass φ (n := n) (χ := χ) ⟨p,hp⟩,rfl⟩

theorem ker_toJacobian (χ : ZMod 3) : (toJacobian φ 6 χ).ker = (normal φ χ).range := by
  ext a
  change toJacobian φ 6 χ a = 0 ↔ ∃ v, normal φ χ v = a
  constructor
  · obtain ⟨p,hp,he⟩ := a.property
    let b : Directions K χ := ⟨p,hp⟩
    have ha : sectionClass φ b = a := Subtype.ext he
    rw [← ha]
    intro hb
    change directionClass φ χ b = 0 at hb
    rw [← LinearMap.mem_ker, ker_directionClass] at hb
    obtain ⟨v,hv⟩ := hb
    exact ⟨velocityClass φ v, (normal_velocityClass φ v).trans (congrArg (sectionClass φ) hv)⟩
  · rintro ⟨w,rfl⟩
    obtain ⟨v,rfl⟩ := velocityClass_surjective φ w
    rw [normal_velocityClass]
    change directionClass φ χ (derivative φ χ v) = 0
    rw [← LinearMap.mem_ker, ker_directionClass]
    exact ⟨v,rfl⟩

def normalQuotientEquiv (χ : ZMod 3) : (piece φ 6 χ ⧸ (normal φ χ).range) ≃ₗ[K] gradedPiece φ 6 χ :=
  (Submodule.quotEquivOfEq _ _ (ker_toJacobian φ χ).symm).trans
    ((toJacobian φ 6 χ).quotKerEquivOfSurjective (toJacobian_surjective φ 6 χ))

end CycleQ2HodgeConeDirections
end

#print axioms CycleQ2HodgeConeDirections.normalQuotientEquiv
