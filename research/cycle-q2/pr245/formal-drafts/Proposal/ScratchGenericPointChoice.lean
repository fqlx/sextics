import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Coefficient fractions in the function field of a monic spatial chart

The three independent coordinates are embedded before adjoining the cubic
root. Passing from polynomial coefficients to their field of fractions
preserves algebraic independence. A derivation vanishing on the coefficient
ring vanishes on this entire coefficient field embedded in the spatial field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GenericSpatialField
open MvPolynomial
open scoped nonZeroDivisors

variable {A K : Type} [CommRing A] [IsDomain A] [Field K]
  (v : MvPolynomial (Fin 3) A →+* K) (hi : Function.Injective v)

def coefficientRing : A →+* K := v.comp C

include hi in
theorem coefficientRing_injective : Function.Injective (coefficientRing v) :=
  hi.comp (C_injective _ _)

def coefficientFraction : FractionRing A →+* K :=
  IsFractionRing.lift (g := coefficientRing v) (coefficientRing_injective v hi)

@[simp] theorem coefficientFraction_algebraMap (a : A) :
    coefficientFraction v hi (algebraMap A (FractionRing A) a) = v (C a) :=
  IsFractionRing.lift_algebraMap _ _

abbrev fieldAlgebra : Algebra (FractionRing A) K := (coefficientFraction v hi).toAlgebra

theorem spatial_independent :
    letI := fieldAlgebra v hi
    AlgebraicIndependent (FractionRing A) (fun j : Fin 3 => v (X j)) := by
  letI := (coefficientRing v).toAlgebra
  letI := fieldAlgebra v hi
  letI : IsScalarTower A (FractionRing A) K :=
    IsScalarTower.of_algebraMap_eq fun a => (coefficientFraction_algebraMap v hi a).symm
  letI : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) A⁰
  have hv : (aeval (fun j : Fin 3 => v (X j)) : MvPolynomial (Fin 3) A →ₐ[A] K).toRingHom = v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (aeval (fun j : Fin 3 => v (X j))) (C a) = _
      rw [aeval_C] <;> rfl
    · intro j
      exact aeval_X _ _
  have hindep : AlgebraicIndependent A (fun j : Fin 3 => v (X j)) := by
    change Function.Injective (aeval (fun j : Fin 3 => v (X j)) : MvPolynomial (Fin 3) A →ₐ[A] K).toRingHom
    rw [hv]
    exact hi
  exact hindep.extendScalars (FractionRing A)

theorem kills_fraction (D : Derivation ℤ K K) (hD : ∀ a : A, D (v (C a)) = 0)
    (a : FractionRing A) : D (coefficientFraction v hi a) = 0 := by
  obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective A a
  rw [map_div₀, coefficientFraction_algebraMap, coefficientFraction_algebraMap,
    Derivation.leibniz_div, hD, hD, smul_zero, smul_zero, sub_self, smul_zero]

/-- The same tuple stays independent after embedding the spatial field into a
compositum and algebraically extending only the coefficients. -/
theorem extend_spatial {F E L : Type} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L] [Algebra E L] [Algebra K L]
    [IsScalarTower F K L] [IsScalarTower F E L] [Algebra.IsAlgebraic F E]
    {x : Fin 3 → K} (hx : AlgebraicIndependent F x) :
    AlgebraicIndependent E (fun j => algebraMap K L (x j)) := by
  let g := IsScalarTower.toAlgHom F K L
  have hx' : AlgebraicIndependent F (g ∘ x) := (g.algebraicIndependent_iff g.injective).mpr hx
  exact hx'.extendScalars E

end CycleQ2GenericSpatialField
end

#print axioms CycleQ2GenericSpatialField.spatial_independent
#print axioms CycleQ2GenericSpatialField.kills_fraction
