import EtaleDerivationUnits

namespace EtaleDerivationLift
variable {A F : Type*} [CommRing A] [Field F]

/-- Ring inverse on a genuine unit maps to the ordinary inverse in every
field factor, so current formulas may be assembled through factor equations. -/
theorem map_ringInverse_to_field (f : A →+* F) (x : A) (hx : IsUnit x) :
    f (Ring.inverse x) = (f x)⁻¹ := by
  apply mul_right_cancel₀ (hx.map f).ne_zero
  rw [← map_mul,Ring.inverse_mul_cancel x hx,map_one,inv_mul_cancel₀ (hx.map f).ne_zero]

#print axioms map_ringInverse_to_field
end EtaleDerivationLift
