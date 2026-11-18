import Proposal.GeometricHodgeEulerSequence
import Proposal.SolutionSupport07Part01
import Mathlib.RingTheory.Localization.Integer

/-!
# Derivations on localizations of the affine hypersurface

The values of a derivation on the four original coordinates form precisely
the kernel of the localized gradient row. To lift a vector, clear the four
denominators and then clear the torsion in its one gradient relation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerLocalizedGradient

open MvPolynomial
open CycleQ2HodgeEulerChartDerivations (Poly Hyp mk mk_equation gradient gradient_apply)
open CycleQ2HodgeEuler (pairing pairing_apply)

variable {K : Type*} [CommRing K] (F : Poly K) (S : Submonoid (Hyp F))
  (B : Type*) [CommRing B] [Algebra (Hyp F) B] [Algebra K B] [IsScalarTower K (Hyp F) B]

private abbrev polynomialMap : Poly K →ₐ[K] B := (IsScalarTower.toAlgHom K (Hyp F) B).comp (mk F)

abbrev gradientRow (j : Fin 4) : B := algebraMap (Hyp F) B (mk F (pderiv j F))

private def coordinates : Derivation K B B →ₗ[B] (Fin 4 → B) where
  toFun D j := D (algebraMap (Hyp F) B (mk F (X j)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem chain (D : Derivation K B B) (p : Poly K) :
    D (algebraMap (Hyp F) B (mk F p)) =
      ∑ j : Fin 4, algebraMap (Hyp F) B (mk F (pderiv j p)) * coordinates F B D j :=
  CycleQ2PolynomialChainRule.apply (polynomialMap F B) D p

private def toKernel : Derivation K B B →ₗ[B] (pairing (gradientRow F B)).ker :=
  (coordinates F B).codRestrict _ (fun D => by
    rw [LinearMap.mem_ker, pairing_apply]
    change (∑ j, algebraMap (Hyp F) B (mk F (pderiv j F)) * coordinates F B D j) = 0
    rw [← chain, mk_equation, map_zero, map_zero])

variable [IsLocalization S B]
include S in
private theorem injective : Function.Injective (toKernel F B) := by
  intro D E h
  have hc : coordinates F B D = coordinates F B E := congrArg Subtype.val h
  have hg : (CycleQ2LocalizationDerivation.graph (S := B) D).toRingHom =
      (CycleQ2LocalizationDerivation.graph (S := B) E).toRingHom := by
    apply IsLocalization.ringHom_ext S
    apply RingHom.ext
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply TrivSqZeroExt.ext
    · rfl
    · change D (algebraMap (Hyp F) B (mk F p)) = E (algebraMap (Hyp F) B (mk F p))
      rw [chain F B D, chain F B E, hc]
  ext b
  exact congrArg TrivSqZeroExt.snd (RingHom.congr_fun hg b)

include S in
private theorem surjective : Function.Surjective (toKernel F B) := by
  intro v
  let φ := algebraMap (Hyp F) B
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite S v.val
  have hnum (j : Fin 4) : ∃ n : Hyp F, φ n = φ d * v.val j := by
    obtain ⟨n, hn⟩ := hd j
    exact ⟨n, by simpa only [Algebra.smul_def] using hn⟩
  choose n hn using hnum
  have hv : ∑ j : Fin 4, φ (mk F (pderiv j F)) * v.val j = 0 :=
    (pairing_apply (gradientRow F B) v.val).symm.trans v.property
  have hz : φ (gradient F n) = 0 := by
    rw [gradient_apply, map_sum]
    calc
      _ = φ d * ∑ j : Fin 4, φ (mk F (pderiv j F)) * v.val j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul, hn, mul_left_comm]
      _ = 0 := by rw [hv, mul_zero]
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff S B _).mp hz
  let w : (gradient F).ker := ⟨(c : Hyp F) • n, by
    rw [LinearMap.mem_ker, map_smul, smul_eq_mul]
    exact hc⟩
  let E := (CycleQ2HodgeEulerChartDerivations.derivationEquiv F).symm w
  have hE (j : Fin 4) : E (mk F (X j)) = (c : Hyp F) * n j := by
    change (CycleQ2HodgeEulerChartDerivations.derivationEquiv F E).val j = _
    rw [show CycleQ2HodgeEulerChartDerivations.derivationEquiv F E = w from
      (CycleQ2HodgeEulerChartDerivations.derivationEquiv F).apply_symm_apply w]
    rfl
  let u := (IsLocalization.map_units B (c * d)).unit
  have hu : (u : B) = φ ((c : Hyp F) * d) := (IsLocalization.map_units B (c * d)).unit_spec
  have hclear (j : Fin 4) : φ (E (mk F (X j))) = (u : B) * v.val j := by
    rw [hE, hu, map_mul, map_mul, hn, mul_assoc]
  refine ⟨(↑(u⁻¹) : B) • CycleQ2LocalizationDerivation.extend (S := B) S E, Subtype.ext (funext fun j => ?_)⟩
  change ↑(u⁻¹) * (CycleQ2LocalizationDerivation.extend (S := B) S E (algebraMap (Hyp F) B (mk F (X j)))) = _
  rw [CycleQ2LocalizationDerivation.extend_map, hclear, ← mul_assoc, Units.inv_mul, one_mul]

/-- Every localized tangent vector is exactly a four-tuple annihilating the
localized gradient. The equivalence is linear over the localization itself. -/
def derivationEquiv : Derivation K B B ≃ₗ[B] (pairing (gradientRow F B)).ker :=
  LinearEquiv.ofBijective (toKernel F B) ⟨injective F S B, surjective F S B⟩

@[simp] theorem derivationEquiv_apply (D : Derivation K B B) (j : Fin 4) :
    (derivationEquiv F S B D).val j = D (algebraMap (Hyp F) B (mk F (X j))) := rfl

end CycleQ2HodgeEulerLocalizedGradient
end

#print axioms CycleQ2HodgeEulerLocalizedGradient.derivationEquiv
