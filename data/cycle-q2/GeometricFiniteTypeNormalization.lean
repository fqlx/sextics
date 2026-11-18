import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Finite normalization of complex affine domains

Noether normalization realizes a finite-type complex domain as an algebra
finite over a polynomial subring. The extension of fraction fields is finite
and separable, so the integral closure is finite over the polynomial ring.
The same generators suffice over the original affine domain.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2FiniteTypeNormalization

open scoped nonZeroDivisors

/-- The integral closure of a complex affine domain in any finite extension
of its fraction field is module-finite. -/
theorem finiteExtensionNormalizationFinite (A L : Type*) [CommRing A] [IsDomain A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] :
    Module.Finite A (integralClosure A L) := by
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  let P := MvPolynomial (Fin n) ℂ
  let K := FractionRing A
  let N := integralClosure A L
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Module.Finite P A := hfin
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr (by
    rw [IsScalarTower.algebraMap_eq P A K]
    exact (IsFractionRing.injective A K).comp hinj)
  let : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  let : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰
  let : Algebra P L := ((algebraMap A L).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A L := IsScalarTower.of_algebraMap_eq' (R := P) (S := A) (A := L) rfl
  let : IsScalarTower P K L := IsScalarTower.to₁₃₄ P A K L
  let : Algebra (FractionRing P) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing P) K)).toAlgebra
  let : IsScalarTower (FractionRing P) K L :=
    IsScalarTower.of_algebraMap_eq' (R := FractionRing P) (S := K) (A := L) rfl
  let : IsScalarTower P (FractionRing P) L := IsScalarTower.to₁₂₄ P (FractionRing P) K L
  let : FiniteDimensional (FractionRing P) L := Module.Finite.trans K L
  let : Algebra P N := ((algebraMap A N).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A N := IsScalarTower.of_algebraMap_eq' (R := P) (S := A) (A := N) rfl
  let : IsScalarTower P N L := IsScalarTower.of_algebraMap_eq' (R := P) (S := N) (A := L) rfl
  let : IsIntegralClosure N P L := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := by
      intro x
      exact ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩,
        fun ⟨y, hy⟩ => hy ▸ isIntegral_trans (R := P) (y : L) y.property⟩ }
  let : Module.Finite P N := IsIntegralClosure.finite P (FractionRing P) L N
  exact Module.Finite.of_restrictScalars_finite P A N

/-- An affine domain of finite type over the complex field has finite normalization. -/
theorem domainNormalizationFinite (A : Type*) [CommRing A] [IsDomain A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  finiteExtensionNormalizationFinite A (FractionRing A)

end CycleQ2FiniteTypeNormalization
end

#print axioms CycleQ2FiniteTypeNormalization.finiteExtensionNormalizationFinite
#print axioms CycleQ2FiniteTypeNormalization.domainNormalizationFinite
