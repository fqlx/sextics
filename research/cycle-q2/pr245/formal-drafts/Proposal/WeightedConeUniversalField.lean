import Proposal.GeometricUniversalWeightedPrimitive
import Proposal.WeightedConeUniversalModel

/-!
# The coefficient-field generic point of the universal normalized sextic

The given monic cubic remains of positive degree after separating the three
spatial variables. Its function field therefore contains the fraction field of
the original coefficient ring. Evaluating at the generic point commutes with
each polynomial and each of its relative partials.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeUniversal

open MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing universalF)
open CycleQ2IncidenceNormalForm
open CycleQ2MonicWeightedAffineEquation (Coeff Coords separate chart universalEquation)
open CycleQ2MonicWeightedPrimitiveSpecialization (Fld ChartRing projection fieldValue)
open CycleQ2MonicWeightedPrimitiveIdentity (Pol b normal density)
open CycleQ2GenericWeightedSpatialDenominator (universalAffine)
open CycleQ2UniversalWeightedTransfer (separate_universal universal_normal_ne_zero)

abbrev FunctionField := Fld universalAffine
abbrev nativeValue := fieldValue universalAffine

def constantValue : Coeff →+* FunctionField := nativeValue.comp C

private theorem degree_pos : 0 < (separate universalAffine).degree := by
  apply Polynomial.natDegree_pos_iff_degree_pos.mp
  rw [separate_universal, CycleQ2MonicWeightedAffineEquation.natDegree] <;> decide

theorem constantValue_injective : Function.Injective constantValue := by
  have h (a : Coeff) : separate (C a : Pol Coeff) = Polynomial.C (C a) :=
    separate.commutes a
  intro a c hac
  apply MvPolynomial.C_injective (Fin 3) Coeff
  apply AdjoinRoot.of.injective_of_degree_ne_zero degree_pos.ne'
  apply IsFractionRing.injective (ChartRing universalAffine) FunctionField
  change algebraMap (ChartRing universalAffine) FunctionField
      (AdjoinRoot.mk _ (separate (C a : Pol Coeff))) =
    algebraMap (ChartRing universalAffine) FunctionField
      (AdjoinRoot.mk _ (separate (C c : Pol Coeff))) at hac
  simpa only [h] using hac

def baseToFunctionField : Base →+* FunctionField :=
  IsFractionRing.lift constantValue_injective

scoped instance baseAlgebra : Algebra Base FunctionField := baseToFunctionField.toAlgebra

def value : Pol Base →+* FunctionField :=
  eval₂Hom baseToFunctionField (fun i => nativeValue (X i))

theorem value_map (p : Pol Coeff) : value (MvPolynomial.map liftCoeff p) = nativeValue p := by
  have h : value.comp (MvPolynomial.map liftCoeff) = nativeValue := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, value, eval₂Hom_C,
        baseToFunctionField, liftCoeff, IsFractionRing.lift_algebraMap] <;> rfl
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, value, eval₂Hom_X']
  exact RingHom.congr_fun h p

theorem chart_equation : CycleQ2HodgeEuler.F coefficients 0 =
    MvPolynomial.map liftCoeff universalAffine :=
  raw_chart_equation

theorem generic_normal : (value.comp (CycleQ2HodgeEuler.dehom 0).toRingHom)
    (pderiv (1 : Fin 5) (CycleQ2GeometricHodgeThreefold.equation coefficients)) ≠ 0 := by
  change value (CycleQ2HodgeEuler.dehom 0 (pderiv 1 _)) ≠ 0
  have hx := CycleQ2HodgeEuler.pderiv_dehom (0 : Fin 4) (0 : Fin 4)
    (CycleQ2GeometricHodgeThreefold.equation coefficients)
  change pderiv 0 _ = CycleQ2HodgeEuler.dehom 0 (pderiv (1 : Fin 5) _) at hx
  rw [← hx]
  change value (pderiv 0 (CycleQ2HodgeEuler.F coefficients 0)) ≠ 0
  rw [chart_equation, pderiv_map, value_map]
  exact universal_normal_ne_zero

theorem native_equation_zero : nativeValue universalAffine = 0 := by
  change algebraMap (ChartRing universalAffine) FunctionField
    (AdjoinRoot.mk (separate universalAffine) (separate universalAffine)) = 0
  rw [AdjoinRoot.mk_self, map_zero]

theorem generic_equation_zero : value (CycleQ2HodgeEuler.F coefficients 0) = 0 := by
  rw [chart_equation, value_map, native_equation_zero]

theorem generic_density : density value (CycleQ2HodgeEuler.F coefficients 0) =
    density nativeValue universalAffine := by
  have hb : (b : Pol Base) = MvPolynomial.map liftCoeff (b : Pol Coeff) := by
    simp only [b, map_mul, map_pow, MvPolynomial.map_X]
  unfold density
  rw [chart_equation, hb]
  simp only [normal, pderiv_map, value_map]

end CycleQ2WeightedConeUniversal
end

#print axioms CycleQ2WeightedConeUniversal.constantValue_injective
#print axioms CycleQ2WeightedConeUniversal.generic_density
