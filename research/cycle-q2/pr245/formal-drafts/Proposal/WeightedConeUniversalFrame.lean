import Proposal.WeightedConeUniversalTangent
import Mathlib.RingTheory.Derivation.Lie

/-! Derivations of the universal monic function field over its coefficient
field are determined by the last three chart coordinates. The implicit
derivations give the dual coordinate frame and commute. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeUniversal

open MvPolynomial
open CycleQ2MonicWeightedAffineEquation (Coeff)
open CycleQ2MonicWeightedPrimitiveIdentity (Pol normal)
open CycleQ2MonicWeightedPrimitiveSpecialization (fieldValue projection ChartRing projection_surjective)
open CycleQ2UniversalWeightedTransfer (universal_normal_ne_zero)
open CycleQ2GenericWeightedSpatialDenominator (universalAffine)
open scoped CycleQ2WeightedConeUniversal

abbrev spatial (j : Fin 3) : FunctionField := nativeValue (X j.succ)

theorem relativeDirection_spatial (j l : Fin 3) :
    relativeDirection j (spatial l) = if l = j then 1 else 0 := by
  have hx : value (X l.succ) = spatial l := eval₂Hom_X' _ _ _
  rw [← hx, relativeDirection_value, pderiv_X_of_ne (Fin.succ_ne_zero l), map_zero, mul_zero, sub_zero]
  by_cases h : l = j
  · subst l
    simp
  · simp [h, pderiv_X_of_ne ((Fin.succ_injective _).ne h)]

private theorem kills_constants (D : Derivation Base FunctionField FunctionField) (c : Coeff) :
    D (nativeValue (C c)) = 0 := by
  have h : baseToFunctionField (liftCoeff c) = nativeValue (C c) :=
    IsFractionRing.lift_algebraMap constantValue_injective c
  rw [← h]
  exact D.map_algebraMap (liftCoeff c)

private theorem one_coordinate (D : Derivation Base FunctionField FunctionField)
    (h : ∀ j, D (spatial j) = 0) (p : Pol Coeff) :
    D (nativeValue p) = nativeValue (pderiv 0 p) * D (nativeValue (X 0)) := by
  have hX (i : Fin 4) : D (nativeValue (X i)) =
      nativeValue (pderiv 0 (X i)) * D (nativeValue (X 0)) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [pderiv_X_self, map_one, one_mul]
    · simp only [pderiv_X_of_ne (Fin.succ_ne_zero j), map_zero, zero_mul]
      exact h j
  induction p using MvPolynomial.induction_on with
  | C c => simp only [kills_constants, pderiv_C, map_zero, zero_mul]
  | add p q hp hq => simp only [map_add, hp, hq, add_mul]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hX j]
    ring

private theorem zero_of_spatial (D : Derivation Base FunctionField FunctionField)
    (h : ∀ j, D (spatial j) = 0) : D = 0 := by
  have hzero := one_coordinate D h universalAffine
  rw [native_equation_zero, map_zero] at hzero
  have h0 : D (nativeValue (X 0)) = 0 :=
    (mul_eq_zero.mp hzero.symm).resolve_left universal_normal_ne_zero
  have hp (q : Pol Coeff) : D (nativeValue q) = 0 := by
    rw [one_coordinate D h q, h0, mul_zero]
  ext z
  obtain ⟨r,s,_,rfl⟩ := IsFractionRing.div_surjective (ChartRing universalAffine) z
  obtain ⟨p,rfl⟩ := projection_surjective universalAffine r
  obtain ⟨q,rfl⟩ := projection_surjective universalAffine s
  change D (nativeValue p / nativeValue q) = 0
  simp only [Derivation.leibniz_div, hp, smul_zero, sub_zero]

theorem spatial_ext {D E : Derivation Base FunctionField FunctionField}
    (h : ∀ i, D (spatial i) = E (spatial i)) : D = E := by
  apply sub_eq_zero.mp
  apply zero_of_spatial
  intro i
  change D (spatial i) - E (spatial i) = 0
  exact sub_eq_zero.mpr (h i)

theorem spatial_expansion (D : Derivation Base FunctionField FunctionField) :
    D = D (spatial 0) • relativeDirection 0 + D (spatial 1) • relativeDirection 1 +
      D (spatial 2) • relativeDirection 2 := by
  apply spatial_ext
  intro i
  fin_cases i <;> simp [Derivation.add_apply, Derivation.smul_apply, relativeDirection_spatial, smul_eq_mul]

theorem relativeDirection_commute (i j : Fin 3) (x : FunctionField) :
    relativeDirection i (relativeDirection j x) = relativeDirection j (relativeDirection i x) := by
  have hh : ⁅relativeDirection i, relativeDirection j⁆ = 0 := by
    apply zero_of_spatial
    intro l
    rw [Derivation.commutator_apply, relativeDirection_spatial, relativeDirection_spatial]
    split_ifs <;> simp
  exact sub_eq_zero.mp (Derivation.congr_fun hh x)

end CycleQ2WeightedConeUniversal
end

#print axioms CycleQ2WeightedConeUniversal.spatial_ext
#print axioms CycleQ2WeightedConeUniversal.spatial_expansion
#print axioms CycleQ2WeightedConeUniversal.relativeDirection_commute
