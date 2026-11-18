import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Specializing finitely many rational functions on a monic cubic chart

The denominator is an element of the hypersurface ring. Its remainder after division
by the equation has three coefficients in the spatial variables. A nonzero scalar
coefficient of one of these polynomials controls specialization of the denominator.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2MonicWeightedDenominator
open scoped nonZeroDivisors
open Polynomial

abbrev Spatial (A : Type*) [CommRing A] := MvPolynomial (Fin 3) A

variable {A B : Type*} [CommRing A] [CommRing B]

abbrev fiber (φ : A →+* B) (f : Polynomial (Spatial A)) := f.map (MvPolynomial.map φ)

def specialize (φ : A →+* B) (f : Polynomial (Spatial A)) :
    AdjoinRoot f →+* AdjoinRoot (fiber φ f) :=
  Ideal.quotientMap _ (Polynomial.mapRingHom (MvPolynomial.map φ)) (by
    apply Ideal.span_le.mpr
    rintro _ (rfl : _ = f)
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp] theorem specialize_mk (φ : A →+* B) (f p : Polynomial (Spatial A)) :
    specialize φ f (AdjoinRoot.mk f p) = AdjoinRoot.mk (fiber φ f) (fiber φ p) := rfl

def slot {f : Polynomial (Spatial A)} (hf : f.Monic) (x : AdjoinRoot f) (i : Fin 3) :
    Spatial A := (AdjoinRoot.modByMonicHom hf x).coeff i.val

theorem slot_specialize (φ : A →+* B) {f : Polynomial (Spatial A)} (hf : f.Monic)
    (x : AdjoinRoot f) (i : Fin 3) :
    slot (hf.map (MvPolynomial.map φ)) (specialize φ f x) i = MvPolynomial.map φ (slot hf x i) := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  change ((AdjoinRoot.modByMonicHom (hf.map (MvPolynomial.map φ)))
      (AdjoinRoot.mk _ (p.map (MvPolynomial.map φ)))).coeff i.val =
    MvPolynomial.map φ (((AdjoinRoot.modByMonicHom hf) (AdjoinRoot.mk f p)).coeff i.val)
  rw [AdjoinRoot.modByMonicHom_mk,AdjoinRoot.modByMonicHom_mk,← Polynomial.map_modByMonic _ hf,
    Polynomial.coeff_map]

theorem exists_detecting_coefficient {f : Polynomial (Spatial A)} (hf : f.Monic)
    (hd : f.natDegree = 3) (x : AdjoinRoot f) (hx : x ≠ 0) :
    ∃ (i : Fin 3) (m : Fin 3 →₀ ℕ), (slot hf x i).coeff m ≠ 0 ∧
      ∀ {B : Type*} [CommRing B] (φ : A →+* B),
        φ ((slot hf x i).coeff m) ≠ 0 → specialize φ f x ≠ 0 := by
  have ex : ∃ j : Fin f.natDegree, (AdjoinRoot.powerBasisAux' hf).repr x j ≠ 0 := by
    by_contra! h
    apply hx
    apply (AdjoinRoot.powerBasisAux' hf).repr.injective
    rw [map_zero]
    apply Finsupp.ext
    intro j
    exact h j
  obtain ⟨j,hj⟩ := ex
  let i : Fin 3 := ⟨j.val, lt_of_lt_of_eq j.isLt hd⟩
  have hs : slot hf x i ≠ 0 := by
    change ((AdjoinRoot.modByMonicHom hf) x).coeff j.val ≠ 0
    simpa only [AdjoinRoot.powerBasisAux'_repr_apply_to_fun] using hj
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero hs
  refine ⟨i,m,hm,?_⟩
  intro B _ φ hφ he
  apply hφ
  rw [← MvPolynomial.coeff_map, ← slot_specialize, he]
  change MvPolynomial.coeff m (((AdjoinRoot.modByMonicHom (hf.map (MvPolynomial.map φ)))
    (0 : AdjoinRoot (f.map (MvPolynomial.map φ)))).coeff i.val) = 0
  rw [(AdjoinRoot.modByMonicHom (hf.map (MvPolynomial.map φ))).map_zero,
    Polynomial.coeff_zero, MvPolynomial.coeff_zero]

/-- In the integral cubic chart, a nonzero denominator divides a nonzero
polynomial involving just the three independent spatial coordinates. -/
theorem exists_spatial_multiple {f : Polynomial (Spatial A)} [Nontrivial A]
    [IsDomain (AdjoinRoot f)] (hf : f.Monic) (d : AdjoinRoot f) (hd : d ≠ 0) :
    ∃ (q : Spatial A) (m : Fin 3 →₀ ℕ), q.coeff m ≠ 0 ∧ d ∣ AdjoinRoot.of f q := by
  let I : Ideal (AdjoinRoot f) := Ideal.span {d}
  letI := hf.finite_adjoinRoot
  have hi := Ideal.comap_ne_bot_of_integral_mem (R := Spatial A) (I := I) hd
    (Ideal.subset_span (Set.mem_singleton d)) (Algebra.IsIntegral.isIntegral d)
  obtain ⟨q,hq,hn⟩ := (I.comap (algebraMap (Spatial A) (AdjoinRoot f))).ne_bot_iff.mp hi
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero hn
  exact ⟨q,m,hm,Ideal.mem_span_singleton.mp hq⟩

/-- Clear every coefficient of the input rational functions by one regular
element of the cubic chart. Its nonvanishing after specialization is detected
on a principal open of the coefficient base. -/
theorem spread_fractions {f : Polynomial (Spatial A)} [Nontrivial (AdjoinRoot f)]
    (hf : f.Monic) (hd : f.natDegree = 3) {ι : Type*} [Finite ι]
    (x : ι → FractionRing (AdjoinRoot f)) :
    ∃ (d : (AdjoinRoot f)⁰) (n : ι → AdjoinRoot f) (a : A), a ≠ 0 ∧
      (∀ i, algebraMap _ (FractionRing (AdjoinRoot f)) (n i) =
        algebraMap _ (FractionRing (AdjoinRoot f)) d.val * x i) ∧
      ∀ {B : Type*} [CommRing B] (φ : A →+* B), φ a ≠ 0 → specialize φ f d.val ≠ 0 := by
  classical
  obtain ⟨d,hdx⟩ := IsLocalization.exist_integer_multiples_of_finite (AdjoinRoot f)⁰ x
  choose n hn using hdx
  obtain ⟨i,m,ha,hφ⟩ := exists_detecting_coefficient hf hd d.val (nonZeroDivisors.coe_ne_zero d)
  refine ⟨d,n,(slot hf d.val i).coeff m,ha,?_,hφ⟩
  intro i
  simpa only [Algebra.smul_def] using hn i

end CycleQ2MonicWeightedDenominator
end

#print axioms CycleQ2MonicWeightedDenominator.exists_detecting_coefficient
#print axioms CycleQ2MonicWeightedDenominator.spread_fractions
#print axioms CycleQ2MonicWeightedDenominator.exists_spatial_multiple
