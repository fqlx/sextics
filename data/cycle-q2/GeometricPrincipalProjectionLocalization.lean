import Proposal.GeometricFamilyDeformation

/-!
# Localizing an additive projection over a principal open

A projection which is linear over the degree-zero ring localizes with its
modules. A single cleared denominator tests equalities after restriction,
even when the homomorphisms act between different coefficient rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2PrincipalProjectionLocalization

variable {A B L : Type*} [CommRing A] [CommRing B] [CommRing L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]

section Localization

variable (p : A) [IsLocalization.Away (algebraMap A B p) L]

theorem base_localizes :
    IsLocalizedModule (Submonoid.powers p) (IsScalarTower.toAlgHom A B L).toLinearMap := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers p)) L := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  infer_instance

/-- Extension of a degree-zero linear map to the localized modules. -/
def projection (P : B →ₗ[A] A) : L →ₗ[A] Localization.Away p := by
  letI := base_localizes (B := B) (L := L) p
  exact IsLocalizedModule.map (Submonoid.powers p) (IsScalarTower.toAlgHom A B L).toLinearMap
    (Algebra.linearMap A (Localization.Away p)) P

theorem projection_base (P : B →ₗ[A] A) (b : B) :
    projection (L := L) p P (algebraMap B L b) = algebraMap A (Localization.Away p) (P b) := by
  letI := base_localizes (B := B) (L := L) p
  exact IsLocalizedModule.map_apply (Submonoid.powers p) (IsScalarTower.toAlgHom A B L).toLinearMap
    (Algebra.linearMap A (Localization.Away p)) P b

end Localization

/-- Equality can be checked before localization when both sides have the
same scalar law and the target inverts the localized element. -/
theorem ext_of_scalar {A M N D : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [CommRing D] (p : A) (j : M →ₗ[A] N)
    [IsLocalizedModule (Submonoid.powers p) j] (f g : N → D) (c : A →+* D)
    (hp : IsUnit (c p)) (hf : ∀ a x, f (a • x) = c a * f x)
    (hg : ∀ a x, g (a • x) = c a * g x) (hbase : ∀ x, f (j x) = g (j x)) (x : N) :
    f x = g x := by
  obtain ⟨⟨b,s⟩,hs⟩ := IsLocalizedModule.surj (Submonoid.powers p) j x
  have hu : IsUnit (c s.val) := by
    obtain ⟨n,hn⟩ := s.property
    rw [← hn, map_pow]
    exact hp.pow n
  apply hu.mul_left_cancel
  change s.val • x = j b at hs
  rw [← hf, ← hg, hs, hbase]

end CycleQ2PrincipalProjectionLocalization
end

#print axioms CycleQ2PrincipalProjectionLocalization.projection_base
#print axioms CycleQ2PrincipalProjectionLocalization.ext_of_scalar
