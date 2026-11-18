import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# A polynomial identity for a primitive of the weighted pole-three residue

On the chart with coordinates (s₁,s₂,s₃,w), eliminate s₁ using its normal
derivative. The three operators are the actual implicit tangent derivations
of the hypersurface function field. For three rational primitive coefficients
with a shared denominator, their divergence equation is equivalent to a
polynomial multiple of the defining equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2MonicWeightedPrimitiveIdentity

open MvPolynomial
abbrev Pol (A : Type*) [CommRing A] := MvPolynomial (Fin 4) A
variable {A B : Type*} [CommRing A] [CommRing B]

def b : Pol A := X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 * X 3 ^ 2

def normal (f : Pol A) := pderiv 0 f

def tangentNumerator (f : Pol A) (j : Fin 3) (p : Pol A) :=
  normal f * pderiv j.succ p - pderiv j.succ f * normal p

def primitiveNumerator (f d : Pol A) (p : Fin 3 → Pol A) :=
  ∑ j, (tangentNumerator f j (p j) * d - p j * tangentNumerator f j d)

def sourceNumerator (f : Pol A) :=
  normal (normal b) * (normal f)^2 -
    (3 * normal b * normal (normal f) + b * normal (normal (normal f))) * normal f +
    3 * b * (normal (normal f))^2

def cleared (f d : Pol A) (p : Fin 3 → Pol A) :=
  2 * (normal f)^4 * primitiveNumerator f d p - d^2 * sourceNumerator f

theorem map_cleared (φ : A →+* B) (f d : Pol A) (p : Fin 3 → Pol A) :
    MvPolynomial.map φ (cleared f d p) =
      cleared (MvPolynomial.map φ f) (MvPolynomial.map φ d) (fun j => MvPolynomial.map φ (p j)) := by
  simp [cleared, primitiveNumerator, tangentNumerator, sourceNumerator, normal, b,
    ← MvPolynomial.pderiv_map, map_sum]

private theorem density_iff {K : Type*} [Field K] [CharZero K]
    (T d n a a₁ a₂ n₁ n₂ : K) (hn : n ≠ 0) (hd : d ≠ 0) :
    T / (n * d^2) = SplitHigherResidue.normalSourceTwo a a₁ a₂ n n₁ n₂ / n ↔
      2*n^4*T - d^2 * (a₂*n^2 - (3*a₁*n₁+a*n₂)*n + 3*a*n₁^2) = 0 := by
  have he : 2*n^5*d^2 * (T / (n*d^2) -
      SplitHigherResidue.normalSourceTwo a a₁ a₂ n n₁ n₂ / n) =
        2*n^4*T - d^2 * (a₂*n^2 - (3*a₁*n₁+a*n₂)*n + 3*a*n₁^2) := by
    unfold SplitHigherResidue.normalSourceTwo
    field_simp [hn,hd]
  have coeff_ne : 2*n^5*d^2 ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ hn)) (pow_ne_zero _ hd)
  rw [← he, mul_eq_zero, or_iff_right coeff_ne, sub_eq_zero]

def density {K : Type*} [Field K] (v : Pol A →+* K) (f : Pol A) :=
  SplitHigherResidue.normalSourceTwo (v b) (v (normal b)) (v (normal (normal b)))
    (v (normal f)) (v (normal (normal f))) (v (normal (normal (normal f)))) / v (normal f)

/-- The pole-three divergence identity over an arbitrary field of evaluation.
The coordinate rule identifies the derivations on polynomial classes; the
quotient rule determines them on the spatial rational functions. -/
theorem divergence_iff_cleared {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra R K]
    (v : Pol A →+* K) (D : Fin 3 → Derivation R K K) (f d : Pol A) (p : Fin 3 → Pol A)
    (hn : v (normal f) ≠ 0) (hd : v d ≠ 0)
    (hD : ∀ j q, D j (v q) = v (pderiv j.succ q) -
      v (pderiv j.succ f) / v (normal f) * v (normal q)) :
    (∑ j, D j (v (p j) / v d)) = density v f ↔ v (cleared f d p) = 0 := by
  have step (j : Fin 3) :
      D j (v (p j) / v d) =
        v (tangentNumerator f j (p j) * d - p j * tangentNumerator f j d) /
          (v (normal f) * v d ^ 2) := by
    rw [Derivation.leibniz_div, hD, hD]
    simp only [tangentNumerator, map_sub, map_mul, smul_eq_mul]
    field_simp [hn,hd]
  simp_rw [step]
  rw [← Finset.sum_div, ← map_sum]
  change v (primitiveNumerator f d p) / (v (normal f) * v d^2) = _ ↔ _
  rw [density, density_iff _ _ _ _ _ _ _ _ hn hd]
  simp only [cleared, sourceNumerator, map_sub, map_add, map_mul, map_pow, map_ofNat]

section Field
variable {S K : Type*} [CommRing S] [IsDomain S] [Field K] [CharZero K]
  [Algebra S K] [IsFractionRing S K]
variable (π : Pol A →+* S) (surj : Function.Surjective π) (f : Pol A)
  (kernel : ∀ q, π q = 0 ↔ f ∣ q)

def value : Pol A →+* K := (algebraMap S K).comp π

variable (hn : value (K := K) π (normal f) ≠ 0)

def tangent (j : Fin 3) : Derivation ℤ K K :=
  HoldoutConstruction.residueTangent π surj ((pderiv 0).restrictScalars ℤ)
    ((pderiv j.succ).restrictScalars ℤ) f kernel hn

omit [CharZero K] in
theorem tangent_apply (j : Fin 3) (q : Pol A) :
    tangent π surj f kernel hn j (value π q) =
      value π (pderiv j.succ q) - value π (pderiv j.succ f) / value π (normal f) * value π (normal q) :=
  HoldoutConstruction.residueTangent_apply π surj _ _ f kernel hn q

theorem primitive_iff_divides (p : Fin 3 → Pol A) (d : Pol A) (hd : value (K := K) π d ≠ 0) :
    (∑ j, tangent π surj f kernel hn j (value π (p j) / value π d)) = density (value π) f ↔
      f ∣ cleared f d p := by
  rw [divergence_iff_cleared (value π) (tangent π surj f kernel hn) f d p hn hd
    (tangent_apply π surj f kernel hn), ← kernel]
  exact IsFractionRing.to_map_eq_zero_iff

end Field
end CycleQ2MonicWeightedPrimitiveIdentity
end

#print axioms CycleQ2MonicWeightedPrimitiveIdentity.divergence_iff_cleared
#print axioms CycleQ2MonicWeightedPrimitiveIdentity.primitive_iff_divides
#print axioms CycleQ2MonicWeightedPrimitiveIdentity.map_cleared
