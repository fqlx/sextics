import Proposal.GeometricIncidenceDehomogenizedChart
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Localization.Basic

/-!
# Homogeneous polynomial presentations of coefficients regular on a cone patch

A presentation records one numerator and its actual allowed denominator.
This data is preserved by partial derivation, including in degrees below the
weight of the chosen variable. It gives an element of the original patch
localization and controls its restrictions to both normalized charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedLocalPresentations
open MvPolynomial CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart

abbrev Poly (k : Type*) [CommRing k] := MvPolynomial (Fin 5) k
def weightZ (j : Fin 5) : ℤ := geometricWeight j

theorem weightZ_eq (e : Fin 5 →₀ ℕ) :
    Finsupp.weight weightZ e = (Finsupp.weight geometricWeight e : ℤ) := by
  rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [weightZ, nsmul_eq_mul]

variable {k B : Type*} [CommRing k] [CommRing B]

theorem integer_degree {p : Poly k} {n : ℕ} (h : p.IsWeightedHomogeneous geometricWeight n) :
    p.IsWeightedHomogeneous weightZ (n : ℤ) := by
  intro e he
  rw [weightZ_eq,h he]

theorem derivative_degree {p : Poly k} {a : ℤ} (hp : p.IsWeightedHomogeneous weightZ a)
    (j : Fin 5) : (pderiv j p).IsWeightedHomogeneous weightZ (a - weightZ j) := by
  intro e he
  rw [MvPolynomial.coeff_pderiv] at he
  have hc : coeff (e + Finsupp.single j 1) p ≠ 0 := by
    intro hz
    exact he (by rw [hz,zero_mul])
  have hd := hp hc
  simp only [map_add,Finsupp.weight_single,one_smul] at hd
  omega

/-- The denominator belongs to exactly the submonoid defining this patch. -/
def Represented (ι : Poly k →+* B) (M : Submonoid (Poly k)) (d : ℤ) (z : B) : Prop :=
  ∃ (p q : Poly k) (a b : ℤ), p.IsWeightedHomogeneous weightZ a ∧
    q.IsWeightedHomogeneous weightZ b ∧ q ∈ M ∧ a-b = d ∧ z * ι q = ι p

namespace Represented
variable {ι : Poly k →+* B} {M : Submonoid (Poly k)} {d e : ℤ} {z v : B}

/-- Quotients and restrictions preserve the same polynomial presentation. -/
theorem map {C' : Type*} [CommRing C'] (h : Represented ι M d z) (g : B →+* C') :
    Represented (g.comp ι) M d (g z) := by
  obtain ⟨p,q,a,b,hp,hq,hm,hd,hz⟩ := h
  refine ⟨p,q,a,b,hp,hq,hm,hd,?_⟩
  change g z * g (ι q) = g (ι p)
  rw [← map_mul,hz]

/-- An injection detects a homogeneous presentation. In particular one can
use an already chosen regular lift of a coefficient computed in the fraction
field. Its image equation recovers the cleared equation in the localization. -/
theorem of_injective_map {C' : Type*} [CommRing C'] (g : B →+* C') (hg : Function.Injective g)
    (h : Represented (g.comp ι) M d (g z)) : Represented ι M d z := by
  obtain ⟨p,q,a,b,hp,hq,hm,hd,hz⟩ := h
  refine ⟨p,q,a,b,hp,hq,hm,hd,hg ?_⟩
  rw [map_mul]
  exact hz

theorem of_localized_image (f : Localization M →+* B) (hf : ∀ p, f (algebraMap (Poly k) _ p) = ι p)
    (hi : Function.Injective f) (c : Localization M) (h : Represented ι M d (f c)) :
    Represented (algebraMap _ _) M d c := by
  apply of_injective_map f hi
  have he : f.comp (algebraMap (Poly k) _) = ι := RingHom.ext hf
  rw [he]
  exact h

theorem zero (ι : Poly k →+* B) (M : Submonoid (Poly k)) (d : ℤ) :
    Represented ι M d 0 :=
  ⟨0,1,d,0,isWeightedHomogeneous_zero _ _ _,isWeightedHomogeneous_one _ _,
    M.one_mem,sub_zero _,by simp⟩

theorem polynomial (ι : Poly k →+* B) (M : Submonoid (Poly k)) (p : Poly k)
    (n : ℕ) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    Represented ι M (n : ℤ) (ι p) :=
  ⟨p,1,n,0,integer_degree hp,isWeightedHomogeneous_one _ _, M.one_mem,sub_zero _,by simp⟩

theorem constant (ι : Poly k →+* B) (M : Submonoid (Poly k)) (c : k) :
    Represented ι M 0 (ι (C c)) := polynomial ι M _ 0 (isWeightedHomogeneous_C _ _)

theorem neg (h : Represented ι M d z) : Represented ι M d (-z) := by
  obtain ⟨p,q,a,b,hp,hq,hm,hd,hz⟩ := h
  exact ⟨-p,q,a,b,hp.neg,hq,hm,hd,by rw [neg_mul,hz,map_neg]⟩

theorem mul (h : Represented ι M d z) (h' : Represented ι M e v) :
    Represented ι M (d+e) (z*v) := by
  obtain ⟨p,q,a,b,hp,hq,hm,hd,hz⟩ := h
  obtain ⟨r,s,c,l,hr,hs,hn,he,hv⟩ := h'
  refine ⟨p*r,q*s,a+c,b+l,hp.mul hr,hq.mul hs,M.mul_mem hm hn,by omega,?_⟩
  rw [map_mul,map_mul,← hz,← hv]
  ring

theorem add (h : Represented ι M d z) (h' : Represented ι M d v) :
    Represented ι M d (z+v) := by
  obtain ⟨p,q,a,b,hp,hq,hm,hd,hz⟩ := h
  obtain ⟨r,s,c,l,hr,hs,hn,he,hv⟩ := h'
  have hrq : (r*q).IsWeightedHomogeneous weightZ (a+l) := by
    rw [show a+l=c+b by omega]
    exact hr.mul hq
  refine ⟨p*s+r*q,q*s,a+l,b+l,(hp.mul hs).add hrq,hq.mul hs,M.mul_mem hm hn,by omega,?_⟩
  rw [map_add,map_mul,map_mul,map_mul,← hz,← hv]
  ring

theorem sub (h : Represented ι M d z) (h' : Represented ι M d v) :
    Represented ι M d (z-v) := by simpa only [sub_eq_add_neg] using h.add h'.neg

/-- Apply the quotient rule after clearing its squared denominator. -/
theorem partial [Algebra k B] (h : Represented ι M d z) (D : Derivation k B B) (j : Fin 5)
    (hD : ∀ p, D (ι p) = ι (pderiv j p)) :
    Represented ι M (d - (geometricWeight j : ℤ)) (D z) := by
  obtain ⟨p,q,a,b,hp,hq,hm,hd,hz⟩ := h
  have hq' : (p * pderiv j q).IsWeightedHomogeneous weightZ (a-weightZ j+b) := by
    rw [show a-weightZ j+b = a+(b-weightZ j) by omega]
    exact hp.mul (derivative_degree hq j)
  refine ⟨pderiv j p*q-p*pderiv j q,q*q,a-weightZ j+b,b+b,
    ((derivative_degree hp j).mul hq).sub hq', hq.mul hq, M.mul_mem hm hm, ?_, ?_⟩
  · change _ = d - weightZ j
    omega
  · have hder := congrArg D hz
    simp only [Derivation.leibniz,smul_eq_mul,hD] at hder
    simp only [map_mul,map_sub]
    linear_combination (ι q)*hder - (ι (pderiv j q))*hz

/-- Any represented coefficient in any target ring has a represented lift
to the actual patch localization, preserved by its map to that target. -/
theorem liftToLocalization (h : Represented ι M d z)
    (f : Localization M →+* B) (hf : ∀ p, f (algebraMap (Poly k) _ p) = ι p) :
    ∃ b : Localization M, Represented (algebraMap _ _) M d b ∧ f b = z := by
  obtain ⟨p,q,a,b,hp,hq,hm,hd,hz⟩ := h
  let denom : M := ⟨q,hm⟩
  let c := IsLocalization.mk' (Localization M) p denom
  have hc : c * algebraMap (Poly k) _ q = algebraMap _ _ p := IsLocalization.mk'_spec _ _ _
  refine ⟨c,⟨p,q,a,b,hp,hq,hm,hd,hc⟩,?_⟩
  have hunit : IsUnit (ι q) := by
    rw [← hf]
    exact (IsLocalization.map_units (Localization M) denom).map f
  apply hunit.mul_right_cancel
  rw [hz,← hf q,← hf p,← map_mul,hc]

end Represented

section Field
variable {K : Type*} [Field K] {ι : Poly k →+* K} {M : Submonoid (Poly k)} {d : ℤ} {z : K}

theorem Represented.dividePolynomial (h : Represented ι M d z) (q : Poly k)
    (n : ℕ) (hq : q.IsWeightedHomogeneous geometricWeight n) (hm : q ∈ M) (hn : ι q ≠ 0) :
    Represented ι M (d-(n : ℤ)) (z / ι q) := by
  have hq' : Represented ι M (-(n : ℤ)) (ι q)⁻¹ :=
    ⟨1,q,0,n,isWeightedHomogeneous_one _ _,integer_degree hq,hm,
      by simp, by simp [hn]⟩
  simpa only [sub_eq_add_neg, div_eq_mul_inv] using h.mul hq'
end Field

section Evaluation
variable {A : Type} [CommRing A] {T : Type*} [CommRing T]

/-- Weighted scalar substitution works over any coefficient ring. -/
private theorem natural_eval_scale (f : A →+* T) (x : Fin 5 → T) (t : T)
    (p : Poly A) (n : ℕ) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    eval₂Hom f (fun j => t ^ geometricWeight j * x j) p = t^n * eval₂Hom f x p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial e c he =>
    have hd : (∑ j ∈ e.support, geometricWeight j * e j) = n := by
      simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using he
    simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, ← pow_mul,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
    ring

/-- The integer degree formula on a unit-scaled chart. A nonzero polynomial
has a monomial of its degree, which recovers the usual natural weighted degree. -/
theorem integer_eval_scale (f : A →+* T) (x : Fin 5 → T) (t : Tˣ)
    (p : Poly A) (a : ℤ) (hp : p.IsWeightedHomogeneous weightZ a) :
    eval₂Hom f (fun j => (t : T)^geometricWeight j * x j) p =
      (↑(t^a) : T) * eval₂Hom f x p := by
  by_cases h : p=0
  · simp [h]
  obtain ⟨e,he⟩ := exists_coeff_ne_zero h
  let n := Finsupp.weight geometricWeight e
  have hn : (n : ℤ) = a := (weightZ_eq e).symm.trans (hp he)
  have hpn : p.IsWeightedHomogeneous geometricWeight n := by
    intro l hl
    exact_mod_cast ((weightZ_eq l).symm.trans ((hp hl).trans hn.symm))
  rw [← hn,zpow_natCast,Units.val_pow_eq_pow_val]
  exact natural_eval_scale f x t p n hpn

/-- Compare both restrictions of any represented coefficient. The coefficient
ring may be a cone quotient or a derivative localization. -/
theorem Represented.normalize {ι : Poly A →+* B} {M : Submonoid (Poly A)}
    {d : ℤ} {z : B} (h : Represented ι M d z)
    (f : A →+* T) (x : Fin 5 → T) (t : Tˣ) (e₀ e₁ : B →+* T)
    (h₀ : ∀ r, e₀ (ι r) = eval₂Hom f x r)
    (h₁ : ∀ r, e₁ (ι r) = eval₂Hom f (fun j => (t : T)^geometricWeight j*x j) r)
    (hu : ∀ q ∈ M, IsUnit (e₁ (ι q))) :
    e₁ z = (↑(t^d) : T) * e₀ z := by
  obtain ⟨p,q,a,b,hp,hq,hm,hd,hz⟩ := h
  have scale (r : Poly A) (c : ℤ) (hr : r.IsWeightedHomogeneous weightZ c) :
      e₁ (ι r) = (↑(t^c) : T) * e₀ (ι r) := by
    rw [h₁,h₀]
    exact integer_eval_scale f x t r c hr
  have hold := congrArg e₀ hz
  have hnew := congrArg e₁ hz
  simp only [map_mul] at hold hnew
  apply (hu q hm).mul_right_cancel
  have hd' : (↑(t^d) : T) * (↑(t^b) : T) = (↑(t^a) : T) := by
    rw [← Units.val_mul, ← zpow_add,show d+b=a by omega]
  rw [hnew,scale p a hp, ← hold,scale q b hq,← hd']
  ring

/-- A coefficient of a horizontal wedge carrying the sum D of its coordinate
weights cancels the change of differential basis. -/
theorem Represented.normalize_coefficient {ι : Poly A →+* B} {M : Submonoid (Poly A)}
    {D : ℕ} {z : B} (h : Represented ι M (-(D : ℤ)) z)
    (f : A →+* T) (x : Fin 5 → T) (t : Tˣ) (e₀ e₁ : B →+* T)
    (h₀ : ∀ r, e₀ (ι r) = eval₂Hom f x r)
    (h₁ : ∀ r, e₁ (ι r) = eval₂Hom f (fun j => (t : T)^geometricWeight j*x j) r)
    (hu : ∀ q ∈ M, IsUnit (e₁ (ι q))) :
    (t : T)^D * e₁ z = e₀ z := by
  rw [h.normalize f x t e₀ e₁ h₀ h₁ hu,zpow_neg,zpow_natCast,← mul_assoc,
    ← Units.val_pow_eq_pow_val,← Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
/-- Evaluation at an actual point of the patch inverts its given denominators. -/
def evaluate (M : Submonoid (Poly A)) (f : A →+* T) (x : Fin 5 → T)
    (hu : ∀ q : M, IsUnit (eval₂Hom f x (q : Poly A))) : Localization M →+* T :=
  IsLocalization.lift (M:=M) (g:=eval₂Hom f x) hu

@[simp] theorem evaluate_polynomial (M : Submonoid (Poly A)) (f : A →+* T)
    (x : Fin 5 → T) (hu : ∀ q : M, IsUnit (eval₂Hom f x (q : Poly A))) (p : Poly A) :
    evaluate M f x hu (algebraMap _ _ p) = eval₂Hom f x p :=
  IsLocalization.lift_eq _ _

/-- Normalizing the pivot preserves the full locus of the homogeneous denominators. -/
theorem scaled_units (M : Submonoid (Poly A)) (f : A →+* T) (x : Fin 5 → T) (t : Tˣ)
    (hM : ∀ q : M, ∃ n : ℕ, (q : Poly A).IsWeightedHomogeneous geometricWeight n)
    (hu : ∀ q : M, IsUnit (eval₂Hom f x (q : Poly A))) (q : M) :
    IsUnit (eval₂Hom f (fun j => (t : T)^geometricWeight j * x j) (q : Poly A)) := by
  obtain ⟨n,hq⟩ := hM q
  rw [natural_eval_scale f x (t : T) q n hq]
  exact (t.isUnit.pow _).mul (hu q)

/-- The unrestricted chart-normalization formula on the patch ring, using
the two canonical maps from the localization. -/
theorem Represented.normalized_evaluation {M : Submonoid (Poly A)}
    {n : ℤ} {z : Localization M} (h : Represented (algebraMap _ _) M n z)
    (f : A →+* T) (x : Fin 5 → T) (t : Tˣ)
    (hM : ∀ q : M, ∃ d : ℕ, (q : Poly A).IsWeightedHomogeneous geometricWeight d)
    (hu : ∀ q : M, IsUnit (eval₂Hom f x (q : Poly A))) :
    evaluate M f (fun j => (t : T)^geometricWeight j * x j) (scaled_units M f x t hM hu) z =
      (↑(t^n) : T) * evaluate M f x hu z := by
  let hy := scaled_units M f x t hM hu
  apply h.normalize f x t (evaluate M f x hu) (evaluate M f _ hy)
    (evaluate_polynomial _ _ _ _) (evaluate_polynomial _ _ _ _)
  intro q hq
  rw [evaluate_polynomial]
  exact hy ⟨q,hq⟩

end Evaluation

end CycleQ2WeightedLocalPresentations
end

#print axioms CycleQ2WeightedLocalPresentations.Represented.partial
#print axioms CycleQ2WeightedLocalPresentations.Represented.liftToLocalization
