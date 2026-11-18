import Proposal.GeometricUniversalWeightedPrimitive
import Proposal.GeometricGenericWeightedSpatialDenominator
import Proposal.GeometricGenericWeightedCleared

/-!
# From a universal weighted primitive to the protected exterior form

A rational three-direction primitive in the universal normalized weighted
chart has polynomial numerators and a common spatial denominator. A nonzero
spatial multiple of the denominator chooses a principal open of the
coefficient space. On a protected deformation meeting that open the three
spatial coordinates remain algebraically independent, so the denominator
survives. The specialized identity supplies an exterior primitive on the
original protected hypersurface through Laurent coefficient extraction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2UniversalWeightedTransfer

open MvPolynomial
  CycleQ2IncidenceNormalForm CycleQ2MonicWeightedAffineEquation
  CycleQ2MonicWeightedPrimitiveSpecialization CycleQ2GenericPencilLift
  CycleQ2GenericWeightedMonicOpen CycleQ2GenericWeightedSpatialDenominator
  CycleQ2GenericWeightedCleared CycleQ2AffineClearing
open CycleQ2MonicWeightedPrimitiveIdentity (map_cleared)
open scoped BigOperators

/-- A rational primitive over the entire normalized coefficient function field suffices
for the original protected exterior form; the primitive may have poles in the deformation. -/
theorem exact_form_of_universal_weighted_primitive (hp : UniversalWeightedPrimitiveExists) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  obtain ⟨v, hv⟩ := hp
  have hm : (separate universalAffine).Monic := by rw [separate_universal]; exact monic _
  have h₃ : (separate universalAffine).natDegree = 3 := by rw [separate_universal]; exact natDegree _
  obtain ⟨a, d, p, q, ha, _, hdiv, hmul, hspec⟩ :=
    spread_with_spatial_multiple hm h₃ universal_normal_ne_zero v hv
  obtain ⟨c, hc, _, _, hL, hgood⟩ := exists_direction_in_monic_open a ha
  let φ := coefficientSpecialization c hc
  have hφ : φ a ≠ 0 := by
    intro hz
    apply hgood
    rw [← coe_coefficientSpecialization c hc a]
    exact congrArg (fun x => (x : CycleQ2GenericSpecialization.RF)) hz
  have hd := spatial_multiple_eval c hc hL hmul (hspec φ hφ).1
  apply exact_form_of_monic_divisibility c hc hL (MvPolynomial.map φ d) (fun j => MvPolynomial.map φ (p j)) hd
  simpa only [φ, map_cleared, map_universal_affine] using map_dvd (MvPolynomial.map φ) hdiv

theorem certificate_of_universal_weighted_primitive (h : UniversalWeightedPrimitiveExists) :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (exact_form_of_universal_weighted_primitive h)

end CycleQ2UniversalWeightedTransfer
end

#print axioms CycleQ2UniversalWeightedTransfer.exact_form_of_universal_weighted_primitive
#print axioms CycleQ2UniversalWeightedTransfer.certificate_of_universal_weighted_primitive
