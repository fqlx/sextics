import Proposal.GeometricHodgeInfinitesimalQuotient
import Proposal.GeometricSquareZeroProjectors

/-!
# Graded coordinate changes over the dual coefficient ring

Substituting Xᵢ + εvᵢ in the actual polynomial algebra over dual numbers
preserves every weighted degree. The square-zero Taylor formula identifies
the image of F − εa and gives the inverse polynomial substitution.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeGradedShear

open MvPolynomial CycleQ2GeometricSurfaceFirstOrder CycleQ2HodgeInfinitesimalQuotient
open CycleQ2GeometricIncidenceProj CycleQ2IncidenceNormalForm
open CycleQ2GenericSexticGradient (CoeffRing)

variable {K : Type} [CommRing K] {χ : ZMod 3}

abbrev P (K : Type) [CommRing K] := MvPolynomial (Fin 5) K
abbrev JD (K : Type) [CommRing K] := P (Dual K)

def liftPoly : P K →+* JD K := MvPolynomial.map (algebraMap K (Dual K))
def eps : JD K := C (TrivSqZeroExt.inr (1 : K))

theorem eps_sq : (eps : JD K) * eps = 0 := by
  rw [eps, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]

def subst (v : Velocities K χ) : JD K →ₐ[Dual K] JD K :=
  aeval (fun i => X i + eps * liftPoly (v i : P K))

@[simp] theorem subst_X (v : Velocities K χ) (i : Fin 5) :
    subst v (X i) = X i + eps * liftPoly (v i : P K) := by simp [subst]

@[simp] theorem subst_eps (v : Velocities K χ) : subst v eps = eps := by simp [subst, eps]

theorem taylor (v : Velocities K χ) (p : P K) :
    subst v (liftPoly p) = liftPoly p + eps * liftPoly (velocityDerivation v p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have h : velocityDerivation v (C c) = 0 := (velocityDerivation v).map_algebraMap c
    simp [liftPoly, h, subst]
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add]
    abel
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, show liftPoly (X i : P K) = X i from map_X _ _, subst_X,
      Derivation.leibniz, velocityDerivation_X]
    simp only [smul_eq_mul, map_add, map_mul, liftPoly, map_X]
    linear_combination (MvPolynomial.map (algebraMap K (Dual K)) (velocityDerivation v p) *
      MvPolynomial.map (algebraMap K (Dual K)) (v i : P K)) * eps_sq (K := K)

theorem subst_inverse_comp (v : Velocities K χ) :
    (subst (-v)).comp (subst v) = AlgHom.id (Dual K) (JD K) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, subst_X, map_add, map_mul, subst_X, subst_eps, taylor]
  change X i + eps * liftPoly (-(v i : P K)) +
    eps * (liftPoly (v i : P K) + eps * liftPoly (velocityDerivation (-v) (v i : P K))) = X i
  rw [map_neg]
  linear_combination liftPoly (velocityDerivation (-v) (v i : P K)) * eps_sq (K := K)

def coordinateEquiv (v : Velocities K χ) : JD K ≃ₐ[Dual K] JD K :=
  AlgEquiv.ofAlgHom (subst v) (subst (-v))
    (by simpa only [neg_neg] using subst_inverse_comp (-v)) (subst_inverse_comp v)

def equation (f a : P K) : JD K := liftPoly f - eps * liftPoly a

theorem subst_equation (v : Velocities K χ) (f a : P K) :
    subst v (equation f a) = equation f (a - velocityDerivation v f) := by
  simp only [equation, map_sub, map_mul, taylor, subst_eps]
  linear_combination -(liftPoly (velocityDerivation v a)) * eps_sq (K := K)

theorem lift_homogeneous {p : P K} {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (liftPoly p).IsWeightedHomogeneous geometricWeight n := by
  intro d hd
  apply hp
  intro h
  exact hd (by simp [liftPoly, coeff_map, h])

theorem subst_homogeneous (v : Velocities K χ) {p : JD K} {n : ℕ}
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (subst v p).IsWeightedHomogeneous geometricWeight n := by
  have hv (i : Fin 5) : (X i + eps * liftPoly (v i : P K)).IsWeightedHomogeneous geometricWeight
      (geometricWeight i) := by
    apply (isWeightedHomogeneous_X _ _ i).add
    have hweight : (fullGrading i).1 = geometricWeight i := by fin_cases i <;> rfl
    rw [← hweight]
    exact (lift_homogeneous (homogeneous_of_character (v i).property)).C_mul
      (TrivSqZeroExt.inr (1 : K))
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using isWeightedHomogeneous_zero (Dual K) geometricWeight n
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
    rw [subst, aeval_monomial]
    change (C c * ∏ i ∈ d.support, (X i + eps * liftPoly (v i : P K)) ^ d i).IsWeightedHomogeneous _ n
    have hprod := (MvPolynomial.IsWeightedHomogeneous.prod d.support
      (fun i => (X i + eps * liftPoly (v i : P K)) ^ d i) (fun i => d i • geometricWeight i)
      (fun i _ => (hv i).pow (d i))).C_mul c
    exact (show ∑ i ∈ d.support, d i • geometricWeight i = n from hd) ▸ hprod

end CycleQ2HodgeGradedShear
end

#print axioms CycleQ2HodgeGradedShear.subst_equation
#print axioms CycleQ2HodgeGradedShear.subst_homogeneous
