import Proposal.WeightedConeUniversalField

/-! The three implicit derivatives of the universal monic hypersurface act on
the same function field over its rational coefficient field. Their action on a
rational primitive is the divergence in the protected universal predicate. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeUniversal

open MvPolynomial
open CycleQ2GenericWeightedSpatialDenominator (universalAffine)
open CycleQ2MonicWeightedPrimitiveSpecialization (direction projection_surjective projection_kernel)
open CycleQ2MonicWeightedPrimitiveIdentity (Pol normal tangent_apply)
open CycleQ2UniversalWeightedTransfer (universal_normal_ne_zero UniversalWeightedPrimitiveExists)

abbrev nativeDirection (j : Fin 3) := direction universalAffine universal_normal_ne_zero j

private theorem nativeDirection_value (j : Fin 3) (p : Pol CycleQ2MonicWeightedAffineEquation.Coeff) :
    nativeDirection j (nativeValue p) = nativeValue (pderiv j.succ p) -
      nativeValue (pderiv j.succ universalAffine) / nativeValue (normal universalAffine) *
        nativeValue (normal p) :=
  tangent_apply _ (projection_surjective _) _ (projection_kernel _) universal_normal_ne_zero j p

theorem nativeDirection_base (j : Fin 3) (a : Base) :
    nativeDirection j (baseToFunctionField a) = 0 := by
  have h (c : CycleQ2MonicWeightedAffineEquation.Coeff) :
      nativeDirection j (constantValue c) = 0 := by
    change nativeDirection j (nativeValue (C c)) = 0
    simp only [nativeDirection_value, normal, pderiv_C, map_zero, mul_zero, sub_zero]
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective CycleQ2MonicWeightedAffineEquation.Coeff a
  simp only [map_div₀, baseToFunctionField, IsFractionRing.lift_algebraMap,
    Derivation.leibniz_div, h, smul_zero, sub_zero]

open scoped CycleQ2WeightedConeUniversal

/-- The original implicit tangent operator, linear over the coefficient field. -/
def relativeDirection (j : Fin 3) : Derivation Base FunctionField FunctionField where
  toFun := nativeDirection j
  map_add' := map_add _
  map_smul' := by
    intro a x
    change nativeDirection j (baseToFunctionField a * x) = baseToFunctionField a * nativeDirection j x
    rw [Derivation.leibniz, nativeDirection_base]
    simp [smul_eq_mul]
  leibniz' := (nativeDirection j).leibniz
  map_one_eq_zero' := (nativeDirection j).map_one_eq_zero

theorem relativeDirection_apply (j : Fin 3) (x : FunctionField) :
    relativeDirection j x = nativeDirection j x := rfl

abbrev affineEquation := CycleQ2HodgeEuler.F coefficients 0

private theorem relativeDirection_mapped (j : Fin 3) (p : Pol CycleQ2MonicWeightedAffineEquation.Coeff) :
    relativeDirection j (value (MvPolynomial.map liftCoeff p)) =
      value (pderiv j.succ (MvPolynomial.map liftCoeff p)) -
        value (pderiv j.succ affineEquation) / value (pderiv 0 affineEquation) *
          value (pderiv 0 (MvPolynomial.map liftCoeff p)) := by
  simp only [relativeDirection_apply, affineEquation, chart_equation, pderiv_map, value_map]
  exact nativeDirection_value j p

theorem relativeDirection_value (j : Fin 3) (p : Pol Base) :
    relativeDirection j (value p) = value (pderiv j.succ p) -
      value (pderiv j.succ affineEquation) / value (pderiv 0 affineEquation) *
        value (pderiv 0 p) := by
  have hx (i : Fin 4) : relativeDirection j (value (X i)) = value (pderiv j.succ (X i)) -
      value (pderiv j.succ affineEquation) / value (pderiv 0 affineEquation) *
        value (pderiv 0 (X i)) := by
    simpa only [MvPolynomial.map_X] using relativeDirection_mapped j (X i)
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [relativeDirection_apply, value, eval₂Hom_C, nativeDirection_base,
      pderiv_C, map_zero, mul_zero, sub_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    ring
  | mul_X p i hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hx]
    ring

/-- Scalar extension to the coefficient field preserves the exact universal
primitive predicate definitionally on the three chosen derivations. -/
theorem relative_primitive_iff :
    (∃ v : Fin 3 → FunctionField,
      ∑ j, relativeDirection j (v j) = CycleQ2MonicWeightedPrimitiveIdentity.density value affineEquation) ↔
    UniversalWeightedPrimitiveExists := by
  simp only [relativeDirection_apply, affineEquation, generic_density] <;> rfl

end CycleQ2WeightedConeUniversal
end

#print axioms CycleQ2WeightedConeUniversal.relativeDirection_value
#print axioms CycleQ2WeightedConeUniversal.relative_primitive_iff
