import Proposal.GeometricGenericWeightedMonicOpen
import Proposal.GeometricGenericWeightedChainRule

/-!
# The coefficient field of the normalized deformed pencil

The leading coefficient and all 44 normalized coefficients are rational
functions of the deformation parameter and weighted pencil ratio. They are
constants for each of the three relative derivations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GenericWeightedMonicCoefficients

open CycleQ2GenericSpecialization (Direction RF parameter)
open CycleQ2GenericWeightedCoordinates (relativeDerivation relative_tau relative_lambda)
open CycleQ2GenericPencilOpen CycleQ2GenericWeightedOpen CycleQ2GenericWeightedMonicOpen
open CycleQ2IncidenceNormalForm

/-- The two-parameter coefficient field inside the actual deformed function field. -/
abbrev coefficientField (d : Direction) :=
  IntermediateField.adjoin ℂ ({parameter d, CycleQ2GenericWeightedCoordinates.lambda} : Set RF)

private theorem polynomial_mem {A : Type} [CommRing A] (d : Direction)
    (φ : Polynomial A →+* RF) (hC : ∀ a, φ (Polynomial.C a) ∈ coefficientField d)
    (hX : φ Polynomial.X ∈ coefficientField d) (p : Polynomial A) :
    φ p ∈ coefficientField d := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact (coefficientField d).add_mem hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    exact (coefficientField d).mul_mem (hC a) ((coefficientField d).pow_mem hX n)

theorem evaluation_mem (d : Direction) (p : TwoParameterRing) :
    evaluation d p ∈ coefficientField d := by
  refine polynomial_mem d (evaluation d) ?_ ?_ p
  · intro a
    change ((evaluation d).comp Polynomial.C) a ∈ coefficientField d
    refine polynomial_mem d ((evaluation d).comp Polynomial.C) ?_ ?_ a
    · intro b
      change evaluation d (constantParameters b) ∈ coefficientField d
      rw [evaluation_constant]
      exact (coefficientField d).algebraMap_mem b
    · change evaluation d CycleQ2GenericPencilOpen.tau ∈ coefficientField d
      rw [evaluation_tau]
      exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  · change evaluation d CycleQ2GenericPencilOpen.lambda ∈ coefficientField d
    rw [evaluation_lambda]
    exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

def leading (d : Direction) (c : ParameterIndex → ℂ) : coefficientField d :=
  ⟨coefficientPoint d c fullSexticLeadingIndex, evaluation_mem _ _⟩

@[simp] theorem leading_coe (d : Direction) (c : ParameterIndex → ℂ) :
    (leading d c : RF) = coefficientPoint d c fullSexticLeadingIndex := rfl

def coefficients (d : Direction) (c : ParameterIndex → ℂ) (e : FullSexticTailIndex) :
    coefficientField d :=
  ⟨normalizedCoefficientPoint d c e, (coefficientField d).div_mem (evaluation_mem _ _)
    (leading d c).property⟩

@[simp] theorem coefficients_coe (d : Direction) (c : ParameterIndex → ℂ) (e : FullSexticTailIndex) :
    (coefficients d c e : RF) = normalizedCoefficientPoint d c e := rfl

theorem deriv_coefficientField (d : Direction) (j : Fin 3) (a : coefficientField d) :
    relativeDerivation d j (a : RF) = 0 :=
  CycleQ2GenericWeightedChainRule.adjoin_parameters_constant _ _ _ (relative_tau d j) (relative_lambda d j) a


@[simp] theorem deriv_leading (d : Direction) (j : Fin 3) (c : ParameterIndex → ℂ) :
    relativeDerivation d j (coefficientPoint d c fullSexticLeadingIndex) = 0 :=
  deriv_coefficientField d j (leading d c)

@[simp] theorem deriv_normalized (d : Direction) (j : Fin 3) (c : ParameterIndex → ℂ)
    (e : FullSexticTailIndex) :
    relativeDerivation d j (normalizedCoefficientPoint d c e) = 0 :=
  deriv_coefficientField d j (coefficients d c e)

end CycleQ2GenericWeightedMonicCoefficients
end

#print axioms CycleQ2GenericWeightedMonicCoefficients.evaluation_mem
#print axioms CycleQ2GenericWeightedMonicCoefficients.deriv_coefficientField
