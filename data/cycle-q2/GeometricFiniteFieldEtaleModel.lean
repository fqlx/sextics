import Proposal.GeometricGenericEtaleBridge
import Proposal.GeometricFinitePrimitivePolynomial

/-!
# A finite characteristic-zero field extension gets an etale polynomial model

Use the genuine primitive element of the original finite field extension,
not an arbitrary unrelated polynomial. Its separable minimal polynomial
satisfies the generic polynomial-to-etale bridge constructed above.

This is the algebraic model needed for the finite residue-field extension
of the selected flag-Hilbert parameter. The primitive generator, degree,
root, derivative, denominators and etale algebra are all conclusions.

Still unproved: identifying the original finite parameter's morphism
with a section over this model after shrinking, the exact generic-fiber
algebra isomorphism, cycle classes, and protected affine residue exactness.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Polynomial
open CycleQ2MonicGenericFiber
open CycleQ2GenericEtaleBridge

namespace CycleQ2FiniteFieldEtaleModel

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero (FractionRing R)]
variable (L : Type*) [Field L] [Algebra (FractionRing R) L]
variable [FiniteDimensional (FractionRing R) L]

/-- A closed algebraic model of an actual finite characteristic-zero field
extension. The chosen polynomial is precisely the primitive element's
minimal polynomial; no auxiliary extension or assumed étale cover appears. -/
theorem exists_primitive_etale_polynomial_model :
    ∃ α : L,
      Algebra.adjoin (FractionRing R) {α} = ⊤ ∧
      (minpoly (FractionRing R) α).natDegree =
        Module.finrank (FractionRing R) L ∧
      aeval α (minpoly (FractionRing R) α) = 0 ∧
      aeval α (derivative (minpoly (FractionRing R) α)) ≠ 0 ∧
      ∃ (d : R) (hd : d ≠ 0),
        ∃ f : Polynomial (Localization.Away d),
          f.Monic ∧ f.map (genericMap d hd) =
              minpoly (FractionRing R) α ∧
          ∃ (r : Localization.Away d), r ≠ 0 ∧
            ∃ P : StandardEtalePair (Localization.Away r),
              P.f = f.map (algebraMap (Localization.Away d) (Localization.Away r)) ∧
              Algebra.Etale (Localization.Away r) P.Ring := by
  obtain ⟨α, hgen, hmonic, hsep, hdegree, hroot, hder⟩ :=
    CycleQ2FinitePrimitivePolynomial.exists_primitive_model (FractionRing R) L
  obtain ⟨d, hd, f, hf, hgeneric, r, hr, P, hP, hEtale⟩ :=
    CycleQ2GenericEtaleBridge.exists_etale_polynomial_model
      (minpoly (FractionRing R) α) hmonic hsep
  exact ⟨α, hgen, hdegree, hroot, hder, d, hd,
    f, hf, hgeneric, r, hr, P, hP, hEtale⟩

end CycleQ2FiniteFieldEtaleModel

end

#print axioms CycleQ2FiniteFieldEtaleModel.exists_primitive_etale_polynomial_model
