import Proposal.GeometricLogarithmicPullback
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Module

/-!
# Uniqueness of regular numerators for actual meromorphic forms

On a localization of a smooth chart, the coordinate differential basis
pulls back to the localized basis. If the coefficients inject, so do all
exterior powers. A simple pole with a specified local equation then has
a unique regular numerator.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogarithmicFractions
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open CycleQ2LogarithmicPullback (differential Forms)

variable {R S M N : Type} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  {ι : Type} [LinearOrder ι] [Fintype ι]

theorem pull_basis (π : R →+* S) (e : M →ₛₗ[π] N)
    (b : Module.Basis ι R M) (c : Module.Basis ι S N) (h : ∀ i, e (b i) = c i) (n : ℕ)
    (j : Set.powersetCard ι n) :
    exteriorMap π e n (b.exteriorPower n j) = c.exteriorPower n j := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family, exteriorMap_wedge, Function.comp_def, h]

theorem pull_injective (π : R →+* S) (hπ : Function.Injective π) (e : M →ₛₗ[π] N)
    (b : Module.Basis ι R M) (c : Module.Basis ι S N) (h : ∀ i, e (b i) = c i) (n : ℕ) :
    Function.Injective (exteriorMap π e n) := by
  classical
  let B := b.exteriorPower n
  let C := c.exteriorPower n
  have hB (i) : exteriorMap π e n (B i) = C i := pull_basis π e b c h n i
  have coord (x : ⋀[R]^n M) (j : Set.powersetCard ι n) :
      C.coord j (exteriorMap π e n x) = π (B.repr x j) := by
    conv_lhs => rw [← B.sum_repr x]
    simp only [map_sum, map_smulₛₗ, hB, map_smul, Module.Basis.coord_apply, smul_eq_mul]
    simp [Module.Basis.repr_self_apply, mul_ite]
  intro x y hxy
  apply B.repr.injective
  ext j
  apply hπ
  rw [← coord, ← coord,hxy]

section Localization
variable {k : Type} [CommRing k] [Algebra k R] [Algebra k S]
  [Algebra R S] [IsScalarTower k R S]
  (P : Submonoid R) [IsLocalization P S]

theorem localized_pull_injective (h : Function.Injective (algebraMap R S))
    (b : Module.Basis ι R (KaehlerDifferential k R)) (n : ℕ) :
    Function.Injective (exteriorMap (algebraMap R S)
      (differential (IsScalarTower.toAlgHom k R S)) n) := by
  let c := b.ofIsLocalizedModule S P (KaehlerDifferential.map k k R S)
  apply pull_injective _ h _ b c _ n
  intro i
  rw [CycleQ2LogarithmicPullback.differential_tower]
  exact (b.ofIsLocalizedModule_apply S P (KaehlerDifferential.map k k R S) i).symm

/-- Inverting a regular equation does not identify different regular
numerators of the same simple pole. -/
theorem simple_fraction_injective (h : Function.Injective (algebraMap R S))
    (b : Module.Basis ι R (KaehlerDifferential k R)) (n : ℕ) (u : Sˣ) :
    Function.Injective (fun m : Forms k R n => (↑u⁻¹ : S) •
      exteriorMap (algebraMap R S) (differential (IsScalarTower.toAlgHom k R S)) n m) := by
  intro x y hxy
  apply localized_pull_injective P h b n
  have h' := congrArg (fun w : Forms k S n => (u : S) • w) hxy
  simpa only [smul_smul,Units.mul_inv,one_smul] using h'

end Localization
end CycleQ2LogarithmicFractions
end

#print axioms CycleQ2LogarithmicFractions.simple_fraction_injective
