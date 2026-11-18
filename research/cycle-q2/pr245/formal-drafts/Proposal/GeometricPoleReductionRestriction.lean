import Proposal.GeometricPoleReductionRadial
import Proposal.GeometricHodgeThreefoldCubicRestriction

/-!
# Restriction of the actual conical derivations to a gradient intersection

A further localization preserves ordinary partial derivatives, the localized
Euler derivation, and the normalized gradient vectors. The proof cancels an
invertible denominator in the derivative of the defining fraction relation.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2PoleReductionRestriction

open MvPolynomial
open CycleQ2PoleReductionGradient
open CycleQ2PoleReductionRadial (radial radial_map)
open CycleQ2GeometricHodgeThreefoldCubic (Inverts extend extend_base)

section Local

variable {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
  [Algebra K B] [Algebra K C] [Algebra A B]

theorem derivation_restrict (S : Submonoid A) [IsLocalization S B] (π : B →+* C)
    (D : Derivation K B B) (E : Derivation K C C)
    (h : ∀ p : A, E (π (algebraMap A B p)) = π (D (algebraMap A B p))) (x : B) :
    E (π x) = π (D x) := by
  obtain ⟨⟨a,d⟩, hx⟩ := IsLocalization.surj S x
  have l := congrArg (fun z => E (π z)) hx
  have r := congrArg (fun z => π (D z)) hx
  change E (π (x * algebraMap A B d.val)) = E (π (algebraMap A B a)) at l
  change π (D (x * algebraMap A B d.val)) = π (D (algebraMap A B a)) at r
  rw [map_mul, Derivation.leibniz, h, h, smul_eq_mul, smul_eq_mul] at l
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul] at r
  exact ((IsLocalization.map_units B d).map π).mul_left_cancel (add_left_cancel (l.trans r.symm))

end Local

variable {K : Type} [CommRing K] {S T : Submonoid (Poly K)}

theorem partial_restrict (b : Inverts S T) (i : Fin 5) (x : Localization S) :
    partial T i (extend b x) = extend b (partial S i x) := by
  apply derivation_restrict S
  intro p
  rw [extend_base, partial_map, partial_map, extend_base]

theorem radial_restrict (b : Inverts S T) (x : Localization S) :
    radial T (extend b x) = extend b (radial S x) := by
  apply derivation_restrict S
  intro p
  rw [extend_base, radial_map, radial_map, extend_base]

theorem normal_clear (S : Submonoid (Poly K)) (G : Poly K) (i : Fin 5) (hi : pderiv i G ∈ S)
    (x : Localization S) :
    algebraMap (Poly K) (Localization S) (pderiv i G) * normal S G i hi x = partial S i x := by
  let u := (IsLocalization.map_units (Localization S) (⟨pderiv i G, hi⟩ : S)).unit
  change (u : Localization S) * ((↑u⁻¹ : Localization S) * partial S i x) = _
  rw [← mul_assoc, u.mul_inv, one_mul]

/-- The chartwise choice of the inverse partial is compatible with every
further localization, including simultaneous gradient intersections. -/
theorem normal_restrict (b : Inverts S T) (G : Poly K) (i : Fin 5)
    (hs : pderiv i G ∈ S) (ht : pderiv i G ∈ T) (x : Localization S) :
    normal T G i ht (extend b x) = extend b (normal S G i hs x) := by
  apply (IsLocalization.map_units (Localization T) (⟨pderiv i G, ht⟩ : T)).mul_left_cancel
  calc
    _ = partial T i (extend b x) := normal_clear T G i ht _
    _ = extend b (partial S i x) := partial_restrict b i x
    _ = extend b (algebraMap (Poly K) (Localization S) (pderiv i G) * normal S G i hs x) :=
      congrArg (extend b) (normal_clear S G i hs x).symm
    _ = _ := by rw [map_mul, extend_base]

end CycleQ2PoleReductionRestriction
end

#print axioms CycleQ2PoleReductionRestriction.partial_restrict
#print axioms CycleQ2PoleReductionRestriction.radial_restrict
#print axioms CycleQ2PoleReductionRestriction.normal_restrict
