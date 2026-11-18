import Proposal.GeometricPoleReductionLocal
import Proposal.GeometricLogarithmicPullback

/-!
# Residue of a logarithmic differential on a smooth hypersurface chart

A simple-pole numerator can be written as the differential of the local
equation wedged with a regular form plus the equation times a regular
form. Insertion of any normalized normal vector followed by restriction
to the hypersurface gives the restriction of the first regular form. This
also proves invariance under multiplication of the local equation by a
unit, including the corresponding scaling of the numerator.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LogarithmicResidue

open CycleQ2LogarithmicPullback (differential differential_D Forms restrict_comp)
open CycleQ2PoleReductionLocal (prepend prepend_generator contract_prepend)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)

section Restriction
variable {R S M N : Type} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
variable (π : R →+* S) (e : M →ₛₗ[π] N)

/-- Taking the exterior pullback commutes with prepending a differential. -/
theorem restrict_prepend (n : ℕ) (a : M) (b : ⋀[R]^n M) :
    exteriorMap π e (n+1) (prepend n a b) = prepend n (e a) (exteriorMap π e n b) := by
  have hb : b ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hb using Submodule.span_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    rw [prepend_generator, exteriorMap_wedge, exteriorMap_wedge, prepend_generator]
    apply congrArg (exteriorPower.ιMulti S (n+1))
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, map_smulₛₗ, hx]

theorem prepend_zero (n : ℕ) (b : ⋀[R]^n M) : prepend n (0 : M) b = 0 := by
  have hb : b ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hb using Submodule.span_induction with
  | mem x h =>
    obtain ⟨m,rfl⟩ := h
    rw [prepend_generator]
    exact (exteriorPower.ιMulti R (n+1)).map_coord_zero 0 rfl
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-- Local residue extracted from a regular numerator of a simple pole. -/
def residue (n : ℕ) (l : M →ₗ[R] R) (m : ⋀[R]^(n+1) M) : ⋀[S]^n N :=
  exteriorMap π e n (interior n l m)

theorem residue_decomposition (n : ℕ) (l : M →ₗ[R] R) (a : M) (f : R)
    (ha : e a = 0) (hf : π f = 0) (b : ⋀[R]^(n+1) M) (c : ⋀[R]^(n+2) M) :
    residue π e (n+1) l (prepend (n+1) a b + f • c) =
      π (l a) • exteriorMap π e (n+1) b := by
  rw [residue, map_add, map_smul, map_add, map_smulₛₗ, hf, zero_smul, add_zero,
    contract_prepend, map_sub, map_smulₛₗ, restrict_prepend, ha, prepend_zero, sub_zero]

end Restriction

section Hypersurface
variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]
variable (π : R →ₐ[k] S)

/-- The residue of m/f across f=0 as an ordinary regular form on that divisor. -/
def localResidue (n : ℕ) (D : Derivation k R R) (m : Forms k R (n+1)) : Forms k S n :=
  residue π.toRingHom (differential π) n D.liftKaehlerDifferential m

@[simp] theorem localResidue_zero (n : ℕ) (D : Derivation k R R) :
    localResidue π n D 0 = 0 := by simp only [localResidue, residue, map_zero]

@[simp] theorem localResidue_add (n : ℕ) (D : Derivation k R R) (a b : Forms k R (n+1)) :
    localResidue π n D (a+b) = localResidue π n D a + localResidue π n D b := by
  simp only [localResidue, residue, map_add]

@[simp] theorem localResidue_neg (n : ℕ) (D : Derivation k R R) (a : Forms k R (n+1)) :
    localResidue π n D (-a) = -localResidue π n D a := by
  simp only [localResidue, residue, map_neg]

@[simp] theorem localResidue_sub (n : ℕ) (D : Derivation k R R) (a b : Forms k R (n+1)) :
    localResidue π n D (a-b) = localResidue π n D a - localResidue π n D b := by
  simp only [localResidue, residue, map_sub]

@[simp] theorem localResidue_smul (n : ℕ) (D : Derivation k R R) (c : R) (a : Forms k R (n+1)) :
    localResidue π n D (c • a) = π c • localResidue π n D a := by
  simp only [localResidue, residue, map_smul, map_smulₛₗ]

theorem localResidue_of_decomposition (n : ℕ) (f : R) (hf : π f = 0)
    (D : Derivation k R R) (hD : D f = 1)
    (m : Forms k R (n+2)) (b : Forms k R (n+1)) (c : Forms k R (n+2))
    (hm : m = prepend (n+1) (KaehlerDifferential.D k R f) b + f • c) :
    localResidue π (n+1) D m = exteriorMap π.toRingHom (differential π) (n+1) b := by
  have ha : differential π (KaehlerDifferential.D k R f) = 0 := by rw [differential_D, hf, map_zero]
  rw [hm, localResidue, residue_decomposition _ _ _ _ _ _ ha hf, Derivation.liftKaehlerDifferential_comp_D, hD, map_one, one_smul]

/-- The simple-pole condition df∧m divisible by f already implies
that every normalized normal vector gives the same regular residue. -/
theorem localResidue_of_log_condition (n : ℕ) (f : R) (hf : π f = 0)
    (D D' : Derivation k R R) (hD : D f = 1) (hD' : D' f = 1)
    (m : Forms k R (n+2)) (v : Forms k R (n+3))
    (hm : prepend (n+2) (KaehlerDifferential.D k R f) m = f • v) :
    localResidue π (n+1) D' m = localResidue π (n+1) D m := by
  have h := CycleQ2PoleReductionLocal.split_pole (n+1) D f hD m v hm
  rw [localResidue_of_decomposition π n f hf D' hD' _ _ _ h,
    localResidue_of_decomposition π n f hf D hD _ _ _ h]

/-- Changing f to u*f multiplies the numerator of the same pole by u.
Even the weaker normalization on the divisor suffices. -/
theorem localResidue_change_equation (n : ℕ) (f u : R) (hf : π f = 0)
    (D D' : Derivation k R R) (hD : D f = 1) (hD' : π (D' (u*f)) = 1)
    (m : Forms k R (n+2)) (b : Forms k R (n+1)) (c : Forms k R (n+2))
    (hm : m = prepend (n+1) (KaehlerDifferential.D k R f) b + f • c) :
    localResidue π (n+1) D' (u • m) = localResidue π (n+1) D m := by
  have hu : π u * π (D' f) = 1 := by
    simpa only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hf, zero_mul, add_zero] using hD'
  have ha : differential π (KaehlerDifferential.D k R f) = 0 := by rw [differential_D, hf, map_zero]
  rw [localResidue_of_decomposition π n f hf D hD m b c hm]
  unfold localResidue residue
  rw [map_smul, map_smulₛₗ]
  change π u • residue π.toRingHom (differential π) (n+1) D'.liftKaehlerDifferential m = _
  rw [hm, residue_decomposition _ _ _ _ _ _ ha hf, Derivation.liftKaehlerDifferential_comp_D,
    smul_smul, hu, one_smul]

/-- Unit changes on chart intersections preserve the residue even when
regular logarithmic lifts have only been certified by divisibility. -/
theorem localResidue_change_of_log_condition (n : ℕ) (f u : R) (hf : π f = 0)
    (D D' : Derivation k R R) (hD : D f = 1) (hD' : π (D' (u*f)) = 1)
    (m : Forms k R (n+2)) (v : Forms k R (n+3))
    (hm : prepend (n+2) (KaehlerDifferential.D k R f) m = f • v) :
    localResidue π (n+1) D' (u • m) = localResidue π (n+1) D m :=
  localResidue_change_equation π n f u hf D D' hD hD' m _ _
    (CycleQ2PoleReductionLocal.split_pole (n+1) D f hD m v hm)

theorem localResidue_normal_coordinate (n : ℕ) (f : R) (hf : π f = 0)
    (D : Derivation k R R) (hD : D f = 1) (g : Fin (n+1) → R) (b : R) :
    localResidue π (n+1) D (prepend (n+1) (KaehlerDifferential.D k R f)
      (b • exteriorPower.ιMulti R (n+1) (fun j => KaehlerDifferential.D k R (g j)))) =
      π b • exteriorPower.ιMulti S (n+1) (fun j => KaehlerDifferential.D k S (π (g j))) := by
  rw [localResidue_of_decomposition π n f hf D hD _ _ 0
    (by rw [smul_zero, add_zero]), map_smulₛₗ, exteriorMap_wedge]
  simp only [differential_D, AlgHom.toRingHom_eq_coe]

/-- Pulling a numerator and its chart equation to a second ambient chart,
then taking residue using a fresh normal, agrees with restriction to the
second divisor. -/
theorem localResidue_restrict {R' S' : Type} [CommRing R'] [CommRing S']
    [Algebra k R'] [Algebra k S'] (π' : R' →ₐ[k] S') (r : R →ₐ[k] R') (s : S →ₐ[k] S')
    (hsq : π'.comp r = s.comp π) (n : ℕ) (f : R) (hf : π f = 0)
    (D : Derivation k R R) (hD : D f = 1) (D' : Derivation k R' R') (hD' : D' (r f) = 1)
    (m : Forms k R (n+2)) (b : Forms k R (n+1)) (c : Forms k R (n+2))
    (hm : m = prepend (n+1) (KaehlerDifferential.D k R f) b + f • c) :
    localResidue π' (n+1) D' (exteriorMap r.toRingHom (differential r) (n+2) m) =
      exteriorMap s.toRingHom (differential s) (n+1) (localResidue π (n+1) D m) := by
  have hf' : π' (r f) = 0 := (congrArg (fun g : R →ₐ[k] S' => g f) hsq).trans
    (by simp only [AlgHom.comp_apply, hf, map_zero])
  have h' := congrArg (exteriorMap r.toRingHom (differential r) (n+2)) hm
  rw [map_add, map_smulₛₗ, restrict_prepend, differential_D] at h'
  rw [localResidue_of_decomposition π' n (r f) hf' D' hD' _ _ _ h',
    localResidue_of_decomposition π n f hf D hD _ _ _ hm,
    ← restrict_comp r π', ← restrict_comp π s, hsq]

/-- Restricting to an intersection may change both the equation and the
normal vector. Their effects cancel on the divisor even if the new normal
is only normalized modulo the equation. -/
theorem localResidue_restrict_unit {R' S' : Type} [CommRing R'] [CommRing S']
    [Algebra k R'] [Algebra k S'] (π' : R' →ₐ[k] S') (r : R →ₐ[k] R') (s : S →ₐ[k] S')
    (hsq : π'.comp r = s.comp π) (n : ℕ) (f : R) (u : R') (hf : π f = 0)
    (D : Derivation k R R) (hD : D f = 1) (D' : Derivation k R' R')
    (hD' : π' (D' (u * r f)) = 1)
    (m : Forms k R (n+2)) (v : Forms k R (n+3))
    (hm : prepend (n+2) (KaehlerDifferential.D k R f) m = f • v) :
    localResidue π' (n+1) D' (u • exteriorMap r.toRingHom (differential r) (n+2) m) =
      exteriorMap s.toRingHom (differential s) (n+1) (localResidue π (n+1) D m) := by
  let b := interior (n+1) D.liftKaehlerDifferential m
  let c := interior (n+2) D.liftKaehlerDifferential v
  have decomp : m = prepend (n+1) (KaehlerDifferential.D k R f) b + f • c :=
    CycleQ2PoleReductionLocal.split_pole (n+1) D f hD m v hm
  have hf' : π' (r f) = 0 := (congrArg (fun g : R →ₐ[k] S' => g f) hsq).trans
    (by simp only [AlgHom.comp_apply, hf, map_zero])
  have ha : differential π' (KaehlerDifferential.D k R' (r f)) = 0 := by
    rw [differential_D, hf', map_zero]
  have hu : π' u * π' (D' (r f)) = 1 := by
    simpa only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hf', zero_mul, add_zero] using hD'
  rw [localResidue_of_decomposition π n f hf D hD m b c decomp]
  unfold localResidue residue
  rw [map_smul, map_smulₛₗ]
  change π' u • residue π'.toRingHom (differential π') (n+1) D'.liftKaehlerDifferential
    (exteriorMap r.toRingHom (differential r) (n+2) m) = _
  have h' := congrArg (exteriorMap r.toRingHom (differential r) (n+2)) decomp
  rw [map_add, map_smulₛₗ, restrict_prepend, differential_D] at h'
  rw [h', residue_decomposition _ _ _ _ _ _ ha hf', Derivation.liftKaehlerDifferential_comp_D,
    smul_smul, hu, one_smul, ← restrict_comp r π', ← restrict_comp π s, hsq]

/-- A regular presentation of a logarithmic form is
dlog(f)∧b+c. Its meromorphic derivative has presentation
dlog(f)∧(-d b)+d c. After restriction to the divisor this accounts for
the minus sign in the residue chain map. -/
theorem localResidue_differential {ι : Type} [LinearOrder ι] [Fintype ι]
    (frame : Module.Basis ι R (KaehlerDifferential k R))
    (z : ι → R) (hz : ∀ i, frame i = KaehlerDifferential.D k R (z i))
    (n : ℕ) (f : R) (hf : π f = 0) (D : Derivation k R R) (hD : D f = 1)
    (dr : Forms k R (n+1) →+ Forms k R (n+2))
    (ds : Forms k S (n+1) →+ Forms k S (n+2))
    (hr : ∀ (a : R) (t : Fin (n+1) → R), dr (a • CycleQ2LogarithmicPullback.exactWedge (k := k) (n+1) t) =
      CycleQ2LogarithmicPullback.exactWedge (k := k) (n+2) (Fin.cons a t))
    (hs : ∀ (a : S) (t : Fin (n+1) → S), ds (a • CycleQ2LogarithmicPullback.exactWedge (k := k) (n+1) t) =
      CycleQ2LogarithmicPullback.exactWedge (k := k) (n+2) (Fin.cons a t))
    (m : Forms k R (n+2)) (b : Forms k R (n+1)) (c : Forms k R (n+2))
    (hm : m = prepend (n+1) (KaehlerDifferential.D k R f) b + f • c)
    (dm dc : Forms k R (n+3))
    (hdm : dm = prepend (n+2) (KaehlerDifferential.D k R f) (-dr b) + f • dc) :
    localResidue π (n+2) D dm = -ds (localResidue π (n+1) D m) := by
  rw [localResidue_of_decomposition π (n+1) f hf D hD dm (-dr b) dc hdm,
    localResidue_of_decomposition π n f hf D hD m b c hm, map_neg,
    CycleQ2LogarithmicPullback.exteriorD_natural π frame z hz (n+1) dr ds hr hs b]

end Hypersurface
end CycleQ2LogarithmicResidue
end

#print axioms CycleQ2LogarithmicResidue.localResidue_of_decomposition
#print axioms CycleQ2LogarithmicResidue.localResidue_change_equation

#print axioms CycleQ2LogarithmicResidue.localResidue_differential
