import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The common fraction field of all nonempty opens given by partial derivatives.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2LocalizationFractionEmbedding

variable {k R : Type} [CommRing k] [CommRing R] [IsDomain R] [Algebra k R]
variable (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
local notation "K" => FractionRing R

/-- The localization at any submonoid of regular elements maps into the same fraction field. -/
def map : Localization M →ₐ[k] K :=
  IsLocalization.liftAlgHom (f := IsScalarTower.toAlgHom k R K) (fun (s : M) =>
    IsLocalization.map_units K (⟨s.1, hM s.2⟩ : nonZeroDivisors R))

@[simp] theorem map_polynomial (r : R) :
    map (k := k) M hM (algebraMap R (Localization M) r) = algebraMap R K r :=
  IsLocalization.lift_eq _ _

theorem injective : Function.Injective (map (k := k) M hM) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq M (map (k := k) M hM).toRingHom).2
  intro a b
  change _ ↔ map (k := k) M hM (algebraMap R (Localization M) a) =
    map (k := k) M hM (algebraMap R (Localization M) b)
  rw [map_polynomial, map_polynomial]
  rw [(IsLocalization.injective (Localization M) hM).eq_iff, (IsFractionRing.injective R K).eq_iff]

abbrev fieldAlgebra : Algebra (Localization M) K := (map (k := k) M hM).toRingHom.toAlgebra

theorem fieldTower :
    letI := fieldAlgebra (k := k) M hM
    IsScalarTower k (Localization M) K := IsScalarTower.of_algHom (map (k := k) M hM)

/-- The same meromorphic field localizes each regular simplex at all of its
nonzero divisors. The identification uses the specified embedding. -/
theorem fieldLocalization :
    letI := fieldAlgebra (k := k) M hM
    IsFractionRing (Localization M) K := by
  letI := fieldAlgebra (k := k) M hM
  letI : IsScalarTower R (Localization M) K :=
    IsScalarTower.of_algebraMap_eq fun r => (map_polynomial (k := k) M hM r).symm
  exact IsFractionRing.isFractionRing_of_isLocalization M (Localization M) K hM

end CycleQ2LocalizationFractionEmbedding
end

#print axioms CycleQ2LocalizationFractionEmbedding.fieldLocalization
