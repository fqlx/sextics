import Proposal.GeometricGenericWeightedField
import Proposal.GeometricGenericWeightedTransfer

/-!
# Specialization of a primitive in the weighted quotient field

A primitive with three coefficients in the weighted field, differentiated
over the rational deformation and pencil parameters, specializes to an
exterior three-form on the protected hypersurface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GenericWeightedFieldTransfer

open CycleQ2IncidenceNormalForm CycleQ2GenericPencilLift CycleQ2GenericWeightedField
  CycleQ2GenericWeightedTransfer CycleQ2AffineClearing
open scoped BigOperators

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)

/-- The exact primitive condition entirely inside the weighted field of the deformed pencil. -/
def WeightedPrimitiveExists : Prop :=
  ∃ v : Fin 3 → field (endpointDirection c hc),
    ∑ j, parameterDeriv c hc j (v j) = density c hc

/-- Three rational coefficients in the actual weighted quotient give the primitive demanded
by the protected exterior-form theorem after Laurent specialization. -/
theorem exact_form_of_weighted_field_primitive (h : WeightedPrimitiveExists c hc) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  obtain ⟨v, hv⟩ := h
  exact exact_form_of_weighted_primitive (endpointDirection c hc)
    ⟨fun j => (v j : CycleQ2GenericSpecialization.RF), divergence_to_ambient c hc v hv⟩

theorem certificate_of_weighted_field_primitive (h : WeightedPrimitiveExists c hc) :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (exact_form_of_weighted_field_primitive c hc h)

end CycleQ2GenericWeightedFieldTransfer
end

#print axioms CycleQ2GenericWeightedFieldTransfer.exact_form_of_weighted_field_primitive
#print axioms CycleQ2GenericWeightedFieldTransfer.certificate_of_weighted_field_primitive
