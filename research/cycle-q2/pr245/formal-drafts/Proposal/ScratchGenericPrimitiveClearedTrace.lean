import Proposal.ScratchGenericPrimitiveTrace
import Proposal.GeometricMonicWeightedPrimitiveIdentity

/-!
# Descending a polynomial primitive on a finite constant-field chart

All tangent values on the base hypersurface are unchanged after extending
the coefficient field. The cleared identity then produces the three
rational primitive coefficients in the new spatial field. Their normalized
traces give the primitive on the original hypersurface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2WeightedGenericPrimitiveTrace
open CycleQ2FiniteDifferentialDescent MvPolynomial
open CycleQ2MonicWeightedPrimitiveIdentity
open scoped BigOperators

variable {A B K L : Type*} [CommRing A] [CommRing B]
  [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]

omit [CharZero K] [FiniteDimensional K L] in
private theorem density_map (φ : A →+* B) (v₀ : Pol A →+* K) (v : Pol B →+* L)
    (hv : ∀ q, v (MvPolynomial.map φ q) = algebraMap K L (v₀ q)) (f : Pol A) :
    density v (MvPolynomial.map φ f) = algebraMap K L (density v₀ f) := by
  have hb : MvPolynomial.map φ (b : Pol A) = (b : Pol B) := by simp [b]
  simp only [density, normal, ← hb, pderiv_map, hv, SplitHigherResidue.normalSourceTwo,
    map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one]

/-- A cleared primitive descending through a finite coefficient extension.
The coordinate hypotheses need only be checked on four generators. -/
theorem descends_of_cleared (φ : A →+* B) (v₀ : Pol A →+* K) (v : Pol B →+* L)
    (hv : ∀ q, v (MvPolynomial.map φ q) = algebraMap K L (v₀ q))
    (D : Fin 3 → Derivation ℤ K K) (f : Pol A) (hf : v₀ f = 0)
    (hn : v₀ (normal f) ≠ 0)
    (hX : ∀ j i, D j (v₀ (X i)) = v₀ (pderiv j.succ (X i)) -
      v₀ (pderiv j.succ f) / v₀ (normal f) * v₀ (normal (X i)))
    (hc : ∀ j c, extend (D j) (v (C c)) = 0)
    (d : Pol B) (p : Fin 3 → Pol B) (hd : v d ≠ 0)
    (hdiv : MvPolynomial.map φ f ∣ cleared (MvPolynomial.map φ f) d p) :
    ∃ u : Fin 3 → K, ∑ j, D j (u j) = density v₀ f := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have hX' (j i) := congrArg (algebraMap K L) (hX j i)
  have hn' : v (normal (MvPolynomial.map φ f)) ≠ 0 := by
    simpa only [normal, pderiv_map, hv, ne_eq, map_eq_zero] using hn
  have hyp (j : Fin 3) (q : Pol B) : extend (D j) (v q) =
      v (pderiv j.succ q) - v (pderiv j.succ (MvPolynomial.map φ f)) /
        v (normal (MvPolynomial.map φ f)) * v (normal q) := by
    apply tangent_rule v (extend (D j)) j _ (hc j) _ q
    intro i
    have e := hX' j i
    simp only [map_sub, map_div₀, map_mul, ← extend_algebraMap, ← hv, normal,
      ← pderiv_map, MvPolynomial.map_X] at e
    simpa only [normal] using e
  have hcleared : v (cleared (MvPolynomial.map φ f) d p) = 0 := by
    obtain ⟨Q, hQ⟩ := hdiv
    rw [hQ, map_mul, hv, hf, map_zero, zero_mul]
  have huv := (divergence_iff_cleared v (fun j => extend (D j)) (MvPolynomial.map φ f)
    d p hn' hd hyp).mpr hcleared
  rw [density_map φ v₀ v hv f] at huv
  exact ⟨_, divergence_descends D (density v₀ f) _ huv⟩


/-- Evaluation in the finite spatial compositum at the original spatial
coordinates and the images of the extended coefficients. -/
def coefficientEvaluation {k E : Type*} [Field k] [Field E] [Algebra k E] [Algebra k L]
    (i : E →ₐ[k] L) (v₀ : Pol A →+* K) : Pol E →+* L :=
  MvPolynomial.eval₂Hom i.toRingHom (fun j => algebraMap K L (v₀ (X j)))

/-- It suffices to give the homomorphism from the finite residue field to
the finite compositum over the generic parameter field. The spatial
coordinates and their four generator derivatives come from the original
hypersurface. -/
theorem descends_of_finite_constant_point
    {k E : Type*} [Field k] [CharZero k] [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] [Algebra k K] [Algebra k L] [IsScalarTower k K L]
    (φ : A →+* k) (i : E →ₐ[k] L) (v₀ : Pol A →+* K)
    (hc₀ : ∀ c, v₀ (C c) = algebraMap k K (φ c))
    (D : Fin 3 → Derivation ℤ K K) (hD₀ : ∀ j c, D j (algebraMap k K c) = 0)
    (f : Pol A) (hf : v₀ f = 0) (hn : v₀ (normal f) ≠ 0)
    (hX : ∀ j a, D j (v₀ (X a)) = v₀ (pderiv j.succ (X a)) -
      v₀ (pderiv j.succ f) / v₀ (normal f) * v₀ (normal (X a)))
    (d : Pol E) (p : Fin 3 → Pol E) (hd : coefficientEvaluation i v₀ d ≠ 0)
    (hdiv : MvPolynomial.map ((algebraMap k E).comp φ) f ∣
      cleared (MvPolynomial.map ((algebraMap k E).comp φ) f) d p) :
    ∃ u : Fin 3 → K, ∑ j, D j (u j) = density v₀ f := by
  apply descends_of_cleared ((algebraMap k E).comp φ) v₀ (coefficientEvaluation i v₀)
    _ D f hf hn hX _ d p hd hdiv
  · intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.map_C, coefficientEvaluation, eval₂Hom_C, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, hc₀,
        ← IsScalarTower.algebraMap_apply]
    | add q r hq hr => simp only [map_add, hq, hr]
    | mul_X q j hq =>
      simp only [map_mul, MvPolynomial.map_X, hq] <;>
        simp only [coefficientEvaluation, MvPolynomial.eval₂Hom_X']
  · intro j c
    simpa only [coefficientEvaluation, MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using extend_kills_coefficient (D j) (hD₀ j) i c

end CycleQ2WeightedGenericPrimitiveTrace
end

#print axioms CycleQ2WeightedGenericPrimitiveTrace.descends_of_cleared
#print axioms CycleQ2WeightedGenericPrimitiveTrace.descends_of_finite_constant_point
