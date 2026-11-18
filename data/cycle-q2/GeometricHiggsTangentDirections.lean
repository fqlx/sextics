import Proposal.GeometricHiggsGradedIndices

/-!
# Actual coefficient directions realizing the tangent monomials

Each enumerated tangent direction varies one independent coefficient of the
universal invariant sextic. Coefficientwise differentiation in that parameter
gives the prescribed degree-six monomial. The affine-line formula works at
every specialization of the coefficient family.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricHiggsTangentDirections

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2FermatHiggs
open CycleQ2GenericSexticGradient (CoeffRing universalF)
open CycleQ2FermatJacobian (exponent)
open CycleQ2HiggsJacobianFrames (exp)
open CycleQ2GeometricHiggsGradedIndices (tangentIndex exp_tangentIndex)

/-- The independent coefficient of the monomial carrying the given tangent label. -/
def parameter (m : Fin 35) : FullInvariantIndex 6 :=
  fullIndexOf (exp (tangentIndex m).val) (tangentIndex m).val.property

@[simp] theorem parameter_exponent (m : Fin 35) :
    fullExponentOf (parameter m).val = exponent (tangentMonomial m) := by
  exact (fullIndexOf_exponent (exp (tangentIndex m).val) (tangentIndex m).val.property).trans
    (exp_tangentIndex m)

theorem parameter_injective : Function.Injective parameter := by
  intro m n h
  apply CycleQ2FermatHiggs.tangent_injective
  funext i
  exact congrArg (fun d : Fin 5 →₀ ℕ => d i)
    ((parameter_exponent m).symm.trans ((congrArg (fun e : FullInvariantIndex 6 =>
      fullExponentOf e.val) h).trans (parameter_exponent n)))

/-- Apply the coefficient-ring partial derivative to each polynomial coefficient. -/
def coefficientDerivative (j : FullInvariantIndex 6) (p : MvPolynomial (Fin 5) CoeffRing) :
    MvPolynomial (Fin 5) CoeffRing :=
  AddMonoidAlgebra.map (pderiv j).toLinearMap.toAddMonoidHom p

@[simp] theorem coeff_coefficientDerivative (j : FullInvariantIndex 6)
    (p : MvPolynomial (Fin 5) CoeffRing) (d : Fin 5 →₀ ℕ) :
    coeff d (coefficientDerivative j p) = pderiv j (coeff d p) := rfl

private theorem derivative_sum {ι : Type} [Fintype ι] (j : FullInvariantIndex 6)
    (p : ι → MvPolynomial (Fin 5) CoeffRing) :
    coefficientDerivative j (∑ i, p i) = ∑ i, coefficientDerivative j (p i) := by
  ext d
  simp only [coeff_coefficientDerivative, coeff_sum, map_sum]

private theorem derivative_monomial (j : FullInvariantIndex 6) (d : Fin 5 →₀ ℕ) (a : CoeffRing) :
    coefficientDerivative j (monomial d a) = monomial d (pderiv j a) := by
  classical
  ext e
  by_cases he : d = e <;> simp [he, coeff_monomial]

theorem universalF_derivative (m : Fin 35) :
    coefficientDerivative (parameter m) universalF = monomial (exponent (tangentMonomial m)) 1 := by
  classical
  rw [universalF, fullInvariantPolynomial, derivative_sum]
  simp only [derivative_monomial]
  rw [Finset.sum_eq_single (parameter m)]
  · rw [pderiv_X_self, parameter_exponent]
  · intro j _ hj
    rw [pderiv_X_of_ne hj, map_zero]
  · simp

/-- Varying this coefficient by `t` changes the actual specialized sextic by
exactly `t` times the corresponding tangent monomial. -/
theorem specialize_along_direction {R : Type*} [CommRing R]
    (a : FullInvariantIndex 6 → R) (m : Fin 35) (t : R) :
    fullInvariantPolynomial 6 (fun j => a j + if j = parameter m then t else 0) =
      fullInvariantPolynomial 6 a + monomial (exponent (tangentMonomial m)) t := by
  classical
  simp only [fullInvariantPolynomial, map_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single (parameter m)]
  · simp [parameter_exponent]
  · intro j _ hj
    simp [hj]
  · simp

theorem universalF_map_along_direction {R : Type*} [CommRing R] [Algebra ℂ R]
    (a : FullInvariantIndex 6 → R) (m : Fin 35) (t : R) :
    MvPolynomial.map (eval₂Hom (algebraMap ℂ R)
        (fun j => a j + if j = parameter m then t else 0)) universalF =
      MvPolynomial.map (eval₂Hom (algebraMap ℂ R) a) universalF +
        monomial (exponent (tangentMonomial m)) t := by
  simpa [universalF, Function.comp_def] using specialize_along_direction a m t

end CycleQ2GeometricHiggsTangentDirections
end

#print axioms CycleQ2GeometricHiggsTangentDirections.universalF_derivative
#print axioms CycleQ2GeometricHiggsTangentDirections.universalF_map_along_direction
