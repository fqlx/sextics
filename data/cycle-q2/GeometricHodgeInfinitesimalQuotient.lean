import Proposal.GeometricHiggsJacobianSpanning

/-!
# Weighted polynomial deformations modulo infinitesimal coordinate changes

For an invariant weighted sextic, a velocity of character χ has coordinate
components of weights 1,1,1,1,2 and the corresponding shifted characters.
Differentiating the actual polynomial along these velocities gives all
degree-six Jacobian relations. The quotient of polynomial deformations by
these derivatives is the corresponding piece of the actual Jacobian ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeInfinitesimalQuotient

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2GenericSexticGradient (CoeffRing universalF)
open CycleQ2HiggsJacobianFrames
open CycleQ2HiggsJacobianMembership (partial_homogeneous membership_iff)

variable {K : Type} [CommRing K]

abbrev FiberPolynomial (φ : CoeffRing →+* K) := MvPolynomial.map φ universalF
abbrev Directions (K : Type) [CommRing K] (χ : ZMod 3) :=
  weightedHomogeneousSubmodule K fullGrading (6, χ)
abbrev Velocities (K : Type) [CommRing K] (χ : ZMod 3) :=
  (i : Fin 5) → weightedHomogeneousSubmodule K fullGrading
    ((fullGrading i).1, χ + (fullGrading i).2)

def velocityDerivation {χ : ZMod 3} (v : Velocities K χ) : Derivation K (Poly K) (Poly K) :=
  ∑ i, (v i : Poly K) • pderiv i

theorem velocityDerivation_apply {χ : ZMod 3} (v : Velocities K χ) (p : Poly K) :
    velocityDerivation v p = ∑ i, (v i : Poly K) * pderiv i p := by
  simpa only [velocityDerivation, Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul] using
    congrFun (map_sum Derivation.coeFnAddMonoidHom
      (fun i => (v i : Poly K) • pderiv i) Finset.univ) p

theorem velocityDerivation_X {χ : ZMod 3} (v : Velocities K χ) (i : Fin 5) :
    velocityDerivation v (X i) = v i := by
  simp [velocityDerivation_apply, pderiv_X, Pi.single_apply, mul_ite]

theorem weight_le_six (i : Fin 5) : (fullGrading i).1 ≤ 6 := by fin_cases i <;> decide

theorem velocity_homogeneous (φ : CoeffRing →+* K) {χ : ZMod 3} (v : Velocities K χ) :
    HG (velocityDerivation v (FiberPolynomial φ)) (6,χ) := by
  rw [velocityDerivation_apply]
  apply (weightedHomogeneousSubmodule K fullGrading (6,χ)).sum_mem
  intro i _
  have h := (show HG (v i : Poly K) _ from (v i).property).mul (partial_homogeneous φ i)
  have he : ((fullGrading i).1, χ + (fullGrading i).2) +
      (6 - (fullGrading i).1, -(fullGrading i).2) = (6,χ) := by
    apply Prod.ext
    · exact Nat.add_sub_of_le (weight_le_six i)
    · change χ + (fullGrading i).2 + -(fullGrading i).2 = χ
      abel
  exact he ▸ h

def derivative (φ : CoeffRing →+* K) (χ : ZMod 3) : Velocities K χ →ₗ[K] Directions K χ where
  toFun v := ⟨velocityDerivation v (FiberPolynomial φ), velocity_homogeneous φ v⟩
  map_add' v w := Subtype.ext (by simp [velocityDerivation_apply, add_mul, Finset.sum_add_distrib])
  map_smul' c v := Subtype.ext (by simp [velocityDerivation_apply, Finset.smul_sum])

def directionClass (φ : CoeffRing →+* K) (χ : ZMod 3) :
    Directions K χ →ₗ[K] gradedPiece φ 6 χ :=
  (((quotientMap φ).toLinearMap.comp (Directions K χ).subtype).codRestrict _
    (fun p => ⟨p.val, p.property, rfl⟩))

theorem directionClass_surjective (φ : CoeffRing →+* K) (χ : ZMod 3) :
    Function.Surjective (directionClass φ χ) := by
  rintro ⟨_,p,hp,rfl⟩
  exact ⟨⟨p,hp⟩,rfl⟩

theorem ker_directionClass (φ : CoeffRing →+* K) (χ : ZMod 3) :
    LinearMap.ker (directionClass φ χ) = LinearMap.range (derivative φ χ) := by
  ext p
  change (directionClass φ χ p = 0) ↔ ∃ v, derivative φ χ v = p
  have hzero : directionClass φ χ p = 0 ↔ p.val ∈ jacobian φ := by
    change (⟨quotientMap φ p.val, _⟩ : gradedPiece φ 6 χ) = 0 ↔ _
    rw [Subtype.ext_iff]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hzero, show jacobian φ = Ideal.span (Set.range (fun i => pderiv i (FiberPolynomial φ))) from rfl,
    membership_iff φ 6 χ p.val p.property]
  constructor
  · rintro ⟨h, hh, _, he⟩
    have hv (i : Fin 5) : HG (h i) ((fullGrading i).1, χ + (fullGrading i).2) := by
      simpa only [Nat.sub_sub_self (weight_le_six i)] using hh i
    refine ⟨fun i => ⟨h i,hv i⟩, Subtype.ext ?_⟩
    exact (velocityDerivation_apply (fun i => ⟨h i,hv i⟩ : Velocities K χ) _).trans he.symm
  · rintro ⟨v,rfl⟩
    refine ⟨fun i => v i, fun i => ?_, fun i hi => ((Nat.not_lt.mpr (Nat.sub_le _ _)) hi).elim, ?_⟩
    · simpa only [Nat.sub_sub_self (weight_le_six i)] using (show HG (v i : Poly K) _ from (v i).property)
    · exact velocityDerivation_apply v _

/-- The embedded first-order polynomial deformation quotient. -/
def quotientEquiv (φ : CoeffRing →+* K) (χ : ZMod 3) :
    (Directions K χ ⧸ LinearMap.range (derivative φ χ)) ≃ₗ[K] gradedPiece φ 6 χ :=
  (Submodule.quotEquivOfEq _ _ (ker_directionClass φ χ).symm).trans
    ((directionClass φ χ).quotKerEquivOfSurjective (directionClass_surjective φ χ))

theorem quotientEquiv_mk (φ : CoeffRing →+* K) (χ : ZMod 3) (p : Directions K χ) :
    quotientEquiv φ χ (Submodule.Quotient.mk p) = directionClass φ χ p := rfl

end CycleQ2HodgeInfinitesimalQuotient
end

#print axioms CycleQ2HodgeInfinitesimalQuotient.quotientEquiv
