import Proposal.GeometricGenericWeightedMonicDensity
import Proposal.GeometricGenericWeightedTransfer

/-!
# Evaluating a cleared primitive on the actual protected deformation

A divisibility identity on the normalized affine weighted equation yields
the protected exterior primitive whenever its common spatial denominator
survives evaluation in the deformed function field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedCleared

open MvPolynomial CycleQ2GenericSpecialization CycleQ2GenericPencilLift
  CycleQ2GenericPencilOpen CycleQ2IncidenceNormalForm CycleQ2GenericWeightedOpen
  CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedMonicCoefficients
  CycleQ2GenericWeightedMonicDensity CycleQ2GenericWeightedTransfer CycleQ2AffineClearing
open CycleQ2MonicWeightedPrimitiveIdentity (Pol cleared divergence_iff_cleared)
open scoped BigOperators

variable (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0)
local notation "ep" => endpointDirection c hc

/-- A primitive for the normalized monic density on this single deformed pencil
specializes to a three-form whose exterior derivative is the protected four-form. -/
theorem exact_form_of_monic_primitive
    (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0)
    (h : ∃ v : Fin 3 → RF, (∑ j, relativeDerivation ep j (v j)) =
      CycleQ2MonicWeightedPrimitiveIdentity.density (value ep) (monicEquation ep c)) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA :=
  exact_form_of_weighted_primitive ep (primitive_of_monic c hc hL h)

/-- Only the specified common denominator is evaluated. The cleared equation passes to
the actual rational-function field by the polynomial evaluation homomorphism. -/
theorem exact_form_of_monic_divisibility
    (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0)
    (d : Pol (coefficientField ep)) (p : Fin 3 → Pol (coefficientField ep))
    (hd : value ep d ≠ 0)
    (h : monicEquation ep c ∣ cleared (monicEquation ep c) d p) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  have he : value ep (cleared (monicEquation ep c) d p) = 0 := by
    obtain ⟨q, hq⟩ := h
    rw [hq, map_mul, value_equation c hc hL, zero_mul]
  apply exact_form_of_monic_primitive c hc hL
  exact ⟨fun j => value ep (p j) / value ep d,
    (divergence_iff_cleared (value ep) (relativeDerivation ep) (monicEquation ep c) d p
      (CycleQ2GenericWeightedMonicDensity.normal_ne_zero c hc hL) hd
      (CycleQ2GenericWeightedMonicDensity.tangent_apply c hc hL)).mpr he⟩

/-- Every nonempty principal open of the normalized coefficient space admits an
actual deformed direction where the normalized primitive equation suffices. -/
theorem exists_monic_direction_with_transfer
    (f : MvPolynomial FullSexticTailIndex ℂ) (hf : f ≠ 0) :
    ∃ (s : ParameterIndex → ℂ) (hs : endpointDifference s ≠ 0),
      s fullSexticLeadingIndex = 1 ∧
      eval (fun e : FullSexticTailIndex => s e.val) f ≠ 0 ∧
      coefficientPoint (endpointDirection s hs) s fullSexticLeadingIndex ≠ 0 ∧
      eval₂Hom (algebraMap ℂ RF)
        (CycleQ2GenericWeightedMonicOpen.normalizedCoefficientPoint (endpointDirection s hs) s) f ≠ 0 ∧
      ((∃ v : Fin 3 → RF, (∑ j, relativeDerivation (endpointDirection s hs) j (v j)) =
          CycleQ2MonicWeightedPrimitiveIdentity.density
            (value (endpointDirection s hs)) (monicEquation (endpointDirection s hs) s)) →
        ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
          CycleQ2AffineExactness.residueSourceForm affineA) := by
  obtain ⟨s, hs, hm, he, hL, hgood⟩ :=
    CycleQ2GenericWeightedMonicOpen.exists_direction_in_monic_open f hf
  exact ⟨s, hs, hm, he, hL, hgood, exact_form_of_monic_primitive s hs hL⟩

end CycleQ2GenericWeightedCleared
end

#print axioms CycleQ2GenericWeightedCleared.exact_form_of_monic_primitive
#print axioms CycleQ2GenericWeightedCleared.exact_form_of_monic_divisibility

#print axioms CycleQ2GenericWeightedCleared.exists_monic_direction_with_transfer
