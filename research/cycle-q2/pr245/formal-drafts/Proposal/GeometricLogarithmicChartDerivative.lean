import Proposal.GeometricLogarithmicResidue
import Proposal.GeometricLogarithmicFractions
import Proposal.ScratchLogChartExact

/-! The residue chain rule for an actual meromorphic exterior derivative on a smooth chart. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LogarithmicChartDerivative

open CycleQ2LogarithmicPullback (Forms differential differential_D exactWedge)
open CycleQ2GeometricExteriorSheaf (exteriorMap)
open CycleQ2PoleReductionLocal (prepend)
open CycleQ2LogarithmicResidue (localResidue localResidue_of_decomposition restrict_prepend)
open CycleQ2LogarithmicDifferential (logarithmic exteriorD)

variable {k R S L : Type} [CommRing k] [CommRing R] [CommRing S] [CommRing L]
  [Algebra k R] [Algebra k S] [Algebra k L]

abbrev pull (π : R →ₐ[k] S) (n : ℕ) :=
  exteriorMap π.toRingHom (differential π) n

variable {I J K : Type} [Fintype I] [LinearOrder I]
  [Fintype J] [LinearOrder J] [Fintype K] [LinearOrder K]

theorem exact_symbol (b : Module.Basis I R (KaehlerDifferential k R))
    (x : I → R) (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (n : ℕ) (a : R) (t : Fin n → R) :
    exteriorD b n (a • exactWedge (k := k) n t) =
      exactWedge (k := k) (n+1) (Fin.cons a t) := by
  rw [exactWedge, CycleQ2LogChartExact.exteriorD_exact_wedge b x hx]
  unfold exactWedge
  apply congrArg (exteriorPower.ιMulti R (n+1))
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Ordinary algebraic exterior differentiation on arbitrary two finite exact
coordinate charts commutes with pullback along every algebra map between them. -/
theorem pull_d (π : R →ₐ[k] S) (b : Module.Basis I R (KaehlerDifferential k R))
    (x : I → R) (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (c : Module.Basis J S (KaehlerDifferential k S))
    (y : J → S) (hy : ∀ i, c i = KaehlerDifferential.D k S (y i))
    (n : ℕ) (ω : Forms k R n) :
    exteriorD c n (pull π n ω) = pull π (n+1) (exteriorD b n ω) :=
  CycleQ2LogarithmicPullback.exteriorD_natural π b x hx n _ _
    (exact_symbol b x hx n) (exact_symbol c y hy n) ω

/-- A regular numerator maps to the actual logarithmic meromorphic form in
the ring where the chart equation is inverted. -/
theorem simple_fraction (ℓ : R →ₐ[k] L) (u : Lˣ) (f : R) (hu : ℓ f = u)
    (n : ℕ) (m : Forms k R (n+1)) (β : Forms k R n) (γ : Forms k R (n+1))
    (hm : m = prepend n (KaehlerDifferential.D k R f) β + f • γ) :
    (↑u⁻¹ : L) • pull ℓ (n+1) m =
      logarithmic u n (pull ℓ n β) + pull ℓ (n+1) γ := by
  unfold pull logarithmic
  rw [hm, map_add, map_smulₛₗ, restrict_prepend, differential_D, smul_add, smul_smul]
  change _ + ((↑u⁻¹ : L) * ℓ f) • _ = _
  rw [hu, u.inv_mul, one_smul]

/-- If m/f is logarithmic and dm/f is its meromorphic exterior derivative,
the residue of dm/f is minus the exterior derivative of the residue of m/f.
Here dm is any regular numerator for that derivative, so the equality is
about the original meromorphic form. -/
theorem residue_d_of_injective (ℓ : R →ₐ[k] L) (inj : ∀ n, Function.Injective (pull ℓ n))
    (π : R →ₐ[k] S) (D : Derivation k R R) (f : R) (hf : π f = 0) (hD : D f = 1)
    (u : Lˣ) (hu : ℓ f = u)
    (b : Module.Basis I R (KaehlerDifferential k R)) (x : I → R)
    (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (c : Module.Basis J S (KaehlerDifferential k S)) (y : J → S)
    (hy : ∀ i, c i = KaehlerDifferential.D k S (y i))
    (e : Module.Basis K L (KaehlerDifferential k L)) (z : K → L)
    (hz : ∀ i, e i = KaehlerDifferential.D k L (z i))
    (n : ℕ) (m : Forms k R (n+2)) (dm : Forms k R (n+3))
    (β : Forms k R (n+1)) (γ : Forms k R (n+2))
    (hm : m = prepend (n+1) (KaehlerDifferential.D k R f) β + f • γ)
    (hdm : (↑u⁻¹ : L) • pull ℓ (n+3) dm =
      exteriorD e (n+2) ((↑u⁻¹ : L) • pull ℓ (n+2) m)) :
    localResidue π (n+2) D dm = -exteriorD c (n+1) (localResidue π (n+1) D m) := by
  let β' := -exteriorD b (n+1) β
  let γ' := exteriorD b (n+2) γ
  let dm' := prepend (n+2) (KaehlerDifferential.D k R f) β' + f • γ'
  have hder : dm = dm' := by
    apply inj (n+3)
    apply (LinearEquiv.smulOfUnit u⁻¹ : Forms k L (n+3) ≃ₗ[L] Forms k L (n+3)).injective
    change (↑u⁻¹ : L) • pull ℓ (n+3) dm = (↑u⁻¹ : L) • pull ℓ (n+3) dm'
    rw [hdm, simple_fraction ℓ u f hu _ _ _ _ hm,
      CycleQ2LogChartExact.exteriorD_logarithmic e z hz,
      simple_fraction ℓ u f hu _ _ β' γ' rfl]
    simp only [β', γ', map_neg, pull_d ℓ b x hx e z hz, logarithmic, smul_neg]
  rw [localResidue_of_decomposition π (n+1) f hf D hD dm β' γ' hder,
    localResidue_of_decomposition π n f hf D hD m β γ hm]
  change pull π (n+2) (-exteriorD b (n+1) β) = -exteriorD c (n+1) (pull π (n+1) β)
  rw [map_neg, pull_d π b x hx c y hy]

/-- Clearing the derivative of a pole of order k+1 at the same pole
order gives the first regular numerator used by every order-reduction step. -/
theorem cleared_pole_derivative_of_injective (ℓ : R →ₐ[k] L) (inj : ∀ n, Function.Injective (pull ℓ n))
    (f : R) (u : Lˣ) (hu : ℓ f = u)
    (b : Module.Basis I R (KaehlerDifferential k R)) (x : I → R)
    (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (e : Module.Basis K L (KaehlerDifferential k L)) (z : K → L)
    (hz : ∀ i, e i = KaehlerDifferential.D k L (z i))
    (k' n : ℕ) (m : Forms k R n) (dm : Forms k R (n+1))
    (hdm : (↑u⁻¹ : L)^(k'+1) • pull ℓ (n+1) dm =
      exteriorD e n ((↑u⁻¹ : L)^(k'+1) • pull ℓ n m)) :
    ((k'+1 : ℕ) : R) • prepend n (KaehlerDifferential.D k R f) m =
      f • (exteriorD b n m - dm) := by
  let v : L := ↑u⁻¹
  have hv : (u : L) * v = 1 := u.mul_inv
  have hvd : KaehlerDifferential.D k L v = -v^2 • KaehlerDifferential.D k L (u : L) :=
    (KaehlerDifferential.D k L).leibniz_of_mul_eq_one u.inv_mul
  have hp : KaehlerDifferential.D k L (v^(k'+1)) =
      -(((k'+1 : ℕ) : L) * v^(k'+2)) • KaehlerDifferential.D k L (u : L) := by
    rw [Derivation.leibniz_pow, hvd, ← Nat.cast_smul_eq_nsmul L, smul_smul, smul_smul]
    simp only [Nat.add_sub_cancel, mul_neg, ← pow_add, mul_assoc]
  have invsq : (u : L)^(k'+2) * v^(k'+2) = 1 := by rw [← mul_pow, hv, one_pow]
  have invone : (u : L)^(k'+2) * v^(k'+1) = (u : L) := by
    rw [pow_succ', mul_assoc, ← mul_pow, hv, one_pow, mul_one]
  change v^(k'+1) • pull ℓ (n+1) dm = exteriorD e n (v^(k'+1) • pull ℓ n m) at hdm
  rw [CycleQ2LogChartExact.exteriorD_leibniz_scalar e, hp,
    CycleQ2LogWedge.prepend_smul, pull_d ℓ b x hx e z hz] at hdm
  have h := congrArg (fun w : Forms k L (n+1) => (u : L)^(k'+2) • w) hdm
  have hmul : (u : L)^(k'+2) * (((k'+1 : ℕ) : L) * v^(k'+2)) = ((k'+1 : ℕ) : L) := by
    rw [mul_left_comm, invsq, mul_one]
  simp only [smul_add, smul_smul, mul_neg, hmul, neg_smul, invone] at h
  apply inj (n+1)
  rw [map_smulₛₗ, restrict_prepend, differential_D, map_smulₛₗ, map_sub, smul_sub]
  change ℓ ((k'+1 : ℕ) : R) •
      prepend n (KaehlerDifferential.D k L (ℓ f)) (pull ℓ n m) =
    ℓ f • pull ℓ (n+1) (exteriorD b n m) -
      ℓ f • pull ℓ (n+1) dm
  rw [map_natCast, hu, h]
  abel

/-- A meromorphic form m/f whose derivative has numerator dm/f satisfies
df∧m = f·(d m - dm) in the regular ring itself. -/
theorem log_condition_of_derivative_of_injective (ℓ : R →ₐ[k] L) (inj : ∀ n, Function.Injective (pull ℓ n))
    (f : R) (u : Lˣ) (hu : ℓ f = u)
    (b : Module.Basis I R (KaehlerDifferential k R)) (x : I → R)
    (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (e : Module.Basis K L (KaehlerDifferential k L)) (z : K → L)
    (hz : ∀ i, e i = KaehlerDifferential.D k L (z i))
    (n : ℕ) (m : Forms k R n) (dm : Forms k R (n+1))
    (hdm : (↑u⁻¹ : L) • pull ℓ (n+1) dm =
      exteriorD e n ((↑u⁻¹ : L) • pull ℓ n m)) :
    prepend n (KaehlerDifferential.D k R f) m = f • (exteriorD b n m - dm) := by
  simpa only [Nat.zero_add, Nat.cast_one, one_smul] using
    cleared_pole_derivative_of_injective ℓ inj f u hu b x hx e z hz 0 n m dm
      (by simpa only [Nat.zero_add, pow_one] using hdm)

/-- Every genuine simple pole with simple-pole derivative has a regular
residue satisfying the signed residue chain rule. Both numerators are
arbitrary regular forms here. -/
theorem residue_d_simple_of_injective (ℓ : R →ₐ[k] L) (inj : ∀ n, Function.Injective (pull ℓ n))
    (π : R →ₐ[k] S) (D : Derivation k R R) (f : R) (hf : π f = 0) (hD : D f = 1)
    (u : Lˣ) (hu : ℓ f = u)
    (b : Module.Basis I R (KaehlerDifferential k R)) (x : I → R)
    (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (c : Module.Basis J S (KaehlerDifferential k S)) (y : J → S)
    (hy : ∀ i, c i = KaehlerDifferential.D k S (y i))
    (e : Module.Basis K L (KaehlerDifferential k L)) (z : K → L)
    (hz : ∀ i, e i = KaehlerDifferential.D k L (z i))
    (n : ℕ) (m : Forms k R (n+2)) (dm : Forms k R (n+3))
    (hdm : (↑u⁻¹ : L) • pull ℓ (n+3) dm =
      exteriorD e (n+2) ((↑u⁻¹ : L) • pull ℓ (n+2) m)) :
    localResidue π (n+2) D dm = -exteriorD c (n+1) (localResidue π (n+1) D m) := by
  have h := log_condition_of_derivative_of_injective ℓ inj f u hu b x hx e z hz (n+2) m dm hdm
  exact residue_d_of_injective ℓ inj π D f hf hD u hu b x hx c y hy e z hz n m dm _ _
    (CycleQ2PoleReductionLocal.split_pole (n+1) D f hD m _ h) hdm

/-- The localization instance supplies the injectivity in the cleared numerator identity. -/
theorem log_condition_of_derivative {P : Submonoid R} [Algebra R L] [IsScalarTower k R L]
    [IsLocalization P L] (inj : Function.Injective (algebraMap R L))
    (f : R) (u : Lˣ) (hu : algebraMap R L f = u)
    (b : Module.Basis I R (KaehlerDifferential k R)) (x : I → R)
    (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (e : Module.Basis K L (KaehlerDifferential k L)) (z : K → L)
    (hz : ∀ i, e i = KaehlerDifferential.D k L (z i))
    (n : ℕ) (m : Forms k R n) (dm : Forms k R (n+1))
    (hdm : (↑u⁻¹ : L) • pull (IsScalarTower.toAlgHom k R L) (n+1) dm =
      exteriorD e n ((↑u⁻¹ : L) • pull (IsScalarTower.toAlgHom k R L) n m)) :
    prepend n (KaehlerDifferential.D k R f) m = f • (exteriorD b n m - dm) :=
  log_condition_of_derivative_of_injective (IsScalarTower.toAlgHom k R L)
    (CycleQ2LogarithmicFractions.localized_pull_injective P inj b) f u hu b x hx e z hz n m dm hdm

/-- Localized version of the residue chain rule. -/
theorem residue_d_of_simple {P : Submonoid R} [Algebra R L] [IsScalarTower k R L]
    [IsLocalization P L] (inj : Function.Injective (algebraMap R L))
    (π : R →ₐ[k] S) (D : Derivation k R R) (f : R) (hf : π f = 0) (hD : D f = 1)
    (u : Lˣ) (hu : algebraMap R L f = u)
    (b : Module.Basis I R (KaehlerDifferential k R)) (x : I → R)
    (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (c : Module.Basis J S (KaehlerDifferential k S)) (y : J → S)
    (hy : ∀ i, c i = KaehlerDifferential.D k S (y i))
    (e : Module.Basis K L (KaehlerDifferential k L)) (z : K → L)
    (hz : ∀ i, e i = KaehlerDifferential.D k L (z i))
    (n : ℕ) (m : Forms k R (n+2)) (dm : Forms k R (n+3))
    (hdm : (↑u⁻¹ : L) • pull (IsScalarTower.toAlgHom k R L) (n+3) dm =
      exteriorD e (n+2) ((↑u⁻¹ : L) • pull (IsScalarTower.toAlgHom k R L) (n+2) m)) :
    localResidue π (n+2) D dm = -exteriorD c (n+1) (localResidue π (n+1) D m) :=
  residue_d_simple_of_injective (IsScalarTower.toAlgHom k R L)
    (CycleQ2LogarithmicFractions.localized_pull_injective P inj b)
    π D f hf hD u hu b x hx c y hy e z hz n m dm hdm

end CycleQ2LogarithmicChartDerivative
end

#print axioms CycleQ2LogarithmicChartDerivative.pull_d
#print axioms CycleQ2LogarithmicChartDerivative.residue_d_of_simple
