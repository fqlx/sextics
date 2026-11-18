import Proposal.ScratchFormalNormalChain
import Proposal.ScratchWeightedNormalResidue
import Proposal.GeometricGenericWeightedMonicDensity
import Proposal.GeometricGenericWeightedTransfer

/-!
# Specializing a vanishing cubic-pole residue class

On one chosen monic deformation, take the coefficient of exponent minus
one in the Laurent expansion of the rational cubic pole. Its class in the
quotient by tangential divergences vanishes precisely when that coefficient
has a rational primitive. Specializing such a primitive gives the
certificate on the original fourfold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2DeformedNormalResidue

open HodgeComputer CycleQ2GenericSpecialization CycleQ2GenericPencilLift
  CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedMonicOpen
  CycleQ2GenericWeightedMonicDensity CycleQ2GenericWeightedTransfer
  CycleQ2FormalNormalChain CycleQ2GenericWeightedOpen CycleQ2IncidenceNormalForm
  CycleQ2GenericPencilOpen (ParameterIndex)
open CycleQ2MonicWeightedPrimitiveIdentity (b density)
open scoped BigOperators

variable (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0)
local notation "ep" => endpointDirection c hc
local notation "Fₘ" => monicEquation ep c

private abbrev spatial (j : Fin 3) : Derivation ℤ RF RF :=
  (relativeDerivation ep j).restrictScalars ℤ

/-- In this quotient a coefficient is zero exactly when it is the sum of
the three derivatives of three rational functions of the deformed pencil. -/
def residueClass : RF ⧸ (tangentialBoundary (spatial c hc)).range :=
  QuotientAddGroup.mk' _
    ((CycleQ2WeightedNormalResidue.meromorphic (value ep) Fₘ b).coeff (-1))

theorem residueClass_zero_iff (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0) :
    residueClass c hc = 0 ↔
      ∃ v : Fin 3 → RF, ∑ j, relativeDerivation ep j (v j) = density (value ep) Fₘ := by
  unfold residueClass
  rw [CycleQ2WeightedNormalResidue.weighted_residue_eq_density _ _
    (value_equation c hc hL) (CycleQ2GenericWeightedMonicDensity.normal_ne_zero c hc hL)]
  exact QuotientAddGroup.eq_zero_iff _

theorem exact_form_of_residueClass_zero (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0)
    (hz : residueClass c hc = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  exact exact_form_of_weighted_primitive ep
    (primitive_of_monic c hc hL ((residueClass_zero_iff c hc hL).mp hz))

theorem protected_certificate_of_residueClass_zero (hL : coefficientPoint ep c fullSexticLeadingIndex ≠ 0)
    (hz : residueClass c hc = 0) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (exact_form_of_residueClass_zero c hc hL hz)

end CycleQ2DeformedNormalResidue
end

#print axioms CycleQ2DeformedNormalResidue.protected_certificate_of_residueClass_zero

