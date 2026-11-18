import Proposal.GeometricMonicWeightedAffineDomain
import Proposal.GeometricMonicWeightedPrimitiveSpecialization

/-!
# Rational primitives on the universal monic weighted hypersurface

The normalized affine equation is a monic cubic over a polynomial ring in
three spatial coordinates and the universal coefficients. Its nonzero first
spatial derivative defines the three tangent derivations of the function field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedSpatialDenominator

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2MonicWeightedAffineEquation
  CycleQ2MonicWeightedPrimitiveIdentity

abbrev universalAffine : Pol Coeff :=
  chart (normalizedFullSextic (fun e : FullSexticTailIndex => (X e : Coeff)))

end CycleQ2GenericWeightedSpatialDenominator

namespace CycleQ2UniversalWeightedTransfer

open MvPolynomial CycleQ2MonicWeightedAffineEquation CycleQ2MonicWeightedPrimitiveSpecialization
  CycleQ2GenericWeightedSpatialDenominator
open CycleQ2MonicWeightedPrimitiveIdentity (normal density)
open scoped BigOperators

theorem separate_universal : separate universalAffine = universalEquation :=
  separate_chart_equation _

instance universalChart_domain : IsDomain (ChartRing universalAffine) := by
  unfold ChartRing
  rw [separate_universal]
  infer_instance

instance universalField_charZero : CharZero (Fld universalAffine) := by
  let φ : ℂ →+* Fld universalAffine := (fieldValue universalAffine).comp
    ((MvPolynomial.C : Coeff →+* MvPolynomial (Fin 4) Coeff).comp MvPolynomial.C)
  exact charZero_of_injective_ringHom φ.injective

theorem universal_normal_ne_zero : fieldValue universalAffine (normal universalAffine) ≠ 0 := by
  change algebraMap (ChartRing universalAffine) (Fld universalAffine)
    (projection universalAffine (normal universalAffine)) ≠ 0
  apply IsFractionRing.to_map_eq_zero_iff.not.mpr
  change AdjoinRoot.mk (separate universalAffine) (separate (normal universalAffine)) ≠ 0
  rw [separate_universal]
  exact CycleQ2MonicWeightedAffineEquation.normal_nonzero

/-- Exactness in the universal three-variable weighted hypersurface function field. -/
def UniversalWeightedPrimitiveExists : Prop :=
  ∃ v : Fin 3 → Fld universalAffine,
    ∑ j, direction universalAffine universal_normal_ne_zero j (v j) =
      density (fieldValue universalAffine) universalAffine

end CycleQ2UniversalWeightedTransfer
end

#print axioms CycleQ2UniversalWeightedTransfer.universal_normal_ne_zero
#print axioms CycleQ2UniversalWeightedTransfer.UniversalWeightedPrimitiveExists
