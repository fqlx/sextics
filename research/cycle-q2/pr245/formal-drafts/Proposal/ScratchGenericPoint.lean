import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Complex.Basic

/-!
# Closed points after extension of the coefficient field

An algebraically independent tuple realizes the rational coefficient field.
A finite collection of coefficients with a marked unit, in a nonzero algebra
of finite type over that field, has a realization over a finite extension
of any new coefficient field. These maps need only agree on the rational
coefficient field. They preserve the marked unit that detects a denominator.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricGenericPoint

open MvPolynomial
open scoped TensorProduct

abbrev ParameterField (ι : Type) := FractionRing (MvPolynomial ι ℚ)

variable {ι : Type} {k : Type} [Field k] [CharZero k]

def parameterMap {c : ι → k} (hc : AlgebraicIndependent ℚ c) : ParameterField ι →+* k :=
  IsFractionRing.lift (g := (aeval c : MvPolynomial ι ℚ →ₐ[ℚ] k).toRingHom)
    (algebraicIndependent_iff_injective_aeval.mp hc)

@[simp] theorem parameterMap_coord {c : ι → k} (hc : AlgebraicIndependent ℚ c) (i : ι) :
    parameterMap hc (algebraMap (MvPolynomial ι ℚ) (ParameterField ι) (X i)) = c i := by
  rw [parameterMap, IsFractionRing.lift_algebraMap]
  exact aeval_X c i

/-- The two structure homomorphisms into a finite common field agree on the
rational coefficient field. The first step works for any finite type algebra
of auxiliary coefficients. -/
structure FinitePoint (F K B : Type) [Field F] [Field K] [CommRing B]
    [Algebra F K] [Algebra F B] where
  carrier : Type
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finite : Module.Finite K carrier]
  fromCoefficients : B →+* carrier
  overBase : ∀ x : F, fromCoefficients (algebraMap F B x) =
    algebraMap K carrier (algebraMap F K x)

attribute [instance] FinitePoint.field FinitePoint.algebra FinitePoint.finite

noncomputable def finitePoint (F K B : Type) [Field F] [Field K] [CommRing B]
    [Algebra F K] [Algebra F B] [Nontrivial B] [Algebra.FiniteType F B] :
    FinitePoint F K B := by
  let T := K ⊗[F] B
  letI : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left F K B
      (algebraMap F B).injective
  let m := Classical.choose (Ideal.exists_maximal T)
  letI : m.IsMaximal := Classical.choose_spec (Ideal.exists_maximal T)
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite K (T ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing K (T ⧸ m)
  let s : B →ₐ[F] T := Algebra.TensorProduct.includeRight
  refine { carrier := T ⧸ m, fromCoefficients := (Ideal.Quotient.mk m).comp s.toRingHom, overBase := ?_ }
  intro x
  change Ideal.Quotient.mk m (s (algebraMap F B x)) = _
  rw [s.commutes, IsScalarTower.algebraMap_apply F K T]
  rfl

theorem finitePoint_preserves_unit {F K B : Type} [Field F] [Field K] [CommRing B]
    [Algebra F K] [Algebra F B] (P : FinitePoint F K B) {u : B} (hu : IsUnit u) :
    P.fromCoefficients u ≠ 0 := (hu.map P.fromCoefficients).ne_zero

/-- An independent complex tuple can supply the source algebra structure.
The destination parameters can be independent over a different constant field. -/
def complexPointAlgebra (c : ι → ℂ) (hc : AlgebraicIndependent ℚ c) :
    Algebra (ParameterField ι) ℂ := (parameterMap hc).toAlgebra

/-- Insert the rational coefficients into the generic complex parameter
field, keeping every indeterminate unchanged. -/
def genericCoefficients : ParameterField ι →+* FractionRing (MvPolynomial ι ℂ) :=
  IsFractionRing.lift (g := (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ))).comp
    (MvPolynomial.map (algebraMap ℚ ℂ))) ((IsFractionRing.injective (MvPolynomial ι ℂ)
    (FractionRing (MvPolynomial ι ℂ))).comp
      (MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective))

@[simp] theorem genericCoefficients_coord (i : ι) :
    genericCoefficients (algebraMap (MvPolynomial ι ℚ) (ParameterField ι) (X i)) =
    algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) (X i) := by
  rw [genericCoefficients, IsFractionRing.lift_algebraMap]
  simp

end CycleQ2GeometricGenericPoint

#print axioms CycleQ2GeometricGenericPoint.finitePoint
#print axioms CycleQ2GeometricGenericPoint.genericCoefficients_coord
