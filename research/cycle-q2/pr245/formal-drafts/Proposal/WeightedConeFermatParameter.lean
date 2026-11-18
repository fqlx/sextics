import Proposal.GeometricHodgeThreefoldProper
import Proposal.GeometricMonicWeightedAffineEquation

/-! The Fermat specialization of the monic coefficient parameter ring. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CycleQ2WeightedConeFermatParameter
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2GenericSexticGradient
  CycleQ2GeometricHodgeThreefold CycleQ2MonicWeightedAffineEquation (Coeff)

def integralFull : MvPolynomial (Fin 5) Coeff := normalizedFullSextic X

/-- The coefficients of the monic generic polynomial, as elements of the
polynomial parameter ring before passing to its function field. -/
def integralParameters : CoeffRing →+* Coeff :=
  eval₂Hom C (fun e => integralFull.coeff (fullExponentOf e.val))

def seed : Coeff →+* ℂ := eval (fun e => fermatCoefficients e.val)

theorem integralFull_map {A : Type} [CommRing A] (f : Coeff →+* A) :
    MvPolynomial.map f integralFull = normalizedFullSextic (fun i => f (X i)) := by
  simp only [integralFull, normalizedFullSextic, map_add, map_monomial, map_sum, map_one]

theorem parameters_map {A : Type} [CommRing A] (f : Coeff →+* A) :
    f.comp integralParameters =
      eval₂Hom (f.comp C)
        (fun e : FullInvariantIndex 6 =>
          (normalizedFullSextic (fun i => f (X i))).coeff (fullExponentOf e.val)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, integralParameters, eval₂Hom_C]
  · intro e
    simp only [RingHom.comp_apply, integralParameters, eval₂Hom_X']
    rw [← coeff_map,integralFull_map]

theorem normalized_fermat :
    normalizedFullSextic (fun e : FullSexticTailIndex => fermatCoefficients e.val) =
      CycleQ2FermatJacobian.fermat := by
  have h : fermatCoefficients fullSexticLeadingIndex = 1 := by
    simpa only [seedEvaluation,vertexCoefficient,eval_X] using seed_vertexCoefficient
  have hn := fullInvariantPolynomial_of_homogeneous fermat_homogeneous
  change fullInvariantPolynomial 6 fermatCoefficients = _ at hn
  rw [fullInvariantPolynomial_sextic,h] at hn
  exact hn

theorem integralFull_seed : MvPolynomial.map seed integralFull = CycleQ2FermatJacobian.fermat := by
  rw [integralFull_map]
  simpa only [seed,eval_X] using normalized_fermat

theorem partial_ne (i : Fin 5) : pderiv i integralFull ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.map seed) h
  rw [← pderiv_map,integralFull_seed,CycleQ2FermatJacobian.derivative_eq,map_zero] at he
  exact (mul_ne_zero (MvPolynomial.C_ne_zero.mpr (CycleQ2FermatJacobian.derivativeScalar_ne_zero i))
    (pow_ne_zero _ (MvPolynomial.X_ne_zero i))) he

theorem seed_parameters : seed.comp integralParameters = seedEvaluation := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,integralParameters,eval₂Hom_C,seed,seedEvaluation,eval_C]
  · intro e
    simp only [RingHom.comp_apply,integralParameters,eval₂Hom_X',seedEvaluation,eval_X]
    rw [← coeff_map,integralFull_seed] <;> rfl

theorem goodParameter_ne : integralParameters goodParameter ≠ 0 := by
  intro he
  have h := congrArg seed he
  rw [← RingHom.comp_apply, seed_parameters, goodParameter_seed, map_zero] at h
  exact one_ne_zero h

end CycleQ2WeightedConeFermatParameter
end
#print axioms CycleQ2WeightedConeFermatParameter.goodParameter_ne
#print axioms CycleQ2WeightedConeFermatParameter.partial_ne

