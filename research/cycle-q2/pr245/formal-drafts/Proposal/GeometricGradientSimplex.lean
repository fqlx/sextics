import Proposal.GeometricGradientDenominators
import Proposal.GeometricPoleReductionGradient
import Mathlib.RingTheory.Localization.Away.Basic

/-! Gradient intersections on the affine cone, with their regular and meromorphic restriction maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GradientSimplex

open MvPolynomial
open CycleQ2WeightedCechPresentations (denominators derivative_mem)

variable {k : Type} [CommRing k]
abbrev Poly (k : Type) [CommRing k] := MvPolynomial (Fin 5) k

variable (G : Poly k)

abbrev Ambient (s : Set (Fin 5)) := Localization (denominators G s)
abbrev f (s : Set (Fin 5)) : Ambient G s := algebraMap (Poly k) (Ambient G s) G
abbrev coord (s : Set (Fin 5)) (i : Fin 5) : Ambient G s := algebraMap (Poly k) _ (X i)
abbrev Divisor (s : Set (Fin 5)) := Ambient G s ⧸ Ideal.span {f G s}
abbrev Complement (s : Set (Fin 5)) := Localization.Away (f G s)
abbrev π (s : Set (Fin 5)) : Ambient G s →ₐ[k] Divisor G s :=
  Ideal.Quotient.mkₐ _ _
abbrev cπ (s : Set (Fin 5)) : Ambient G s →ₐ[k] Complement G s :=
  IsScalarTower.toAlgHom _ _ _

@[simp] theorem π_f (s : Set (Fin 5)) : π G s (f G s) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

def fUnit (s : Set (Fin 5)) : (Complement G s)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Complement G s) (f G s)).unit

@[simp] theorem fUnit_val (s : Set (Fin 5)) : (fUnit G s : Complement G s) = cπ G s (f G s) :=
  IsUnit.unit_spec _

abbrev ambientBasis (s : Set (Fin 5)) :=
  CycleQ2PoleReductionGradient.coordinates (denominators G s)

@[simp] theorem ambientBasis_apply (s : Set (Fin 5)) (i : Fin 5) :
    ambientBasis G s i = KaehlerDifferential.D k (Ambient G s) (coord G s i) :=
  CycleQ2PoleReductionGradient.coordinates_apply _ _

def complementBasis (s : Set (Fin 5)) :
    Module.Basis (Fin 5) (Complement G s) (KaehlerDifferential k (Complement G s)) :=
  (ambientBasis G s).ofIsLocalizedModule (Complement G s) (Submonoid.powers (f G s))
    (KaehlerDifferential.map k k (Ambient G s) (Complement G s))

@[simp] theorem complementBasis_apply (s : Set (Fin 5)) (i : Fin 5) :
    complementBasis G s i = KaehlerDifferential.D k _ (cπ G s (coord G s i)) := by
  rw [complementBasis, Module.Basis.ofIsLocalizedModule_apply, ambientBasis_apply,
    KaehlerDifferential.map_D] <;> rfl

abbrev normal (s : Set (Fin 5)) (i : Fin 5) (hi : i ∈ s) :=
  CycleQ2PoleReductionGradient.normal (denominators G s) G i (derivative_mem G hi)

@[simp] theorem normal_f (s : Set (Fin 5)) (i : Fin 5) (hi : i ∈ s) :
    normal G s i hi (f G s) = 1 :=
  CycleQ2PoleReductionGradient.normal_equation _ _ _ _

def indices {n : ℕ} (v : Fin n → Fin 5) : Set (Fin 5) := Set.range v

theorem face_indices {m n : ℕ} (v : Fin n → Fin 5) (u : Fin m → Fin n) :
    indices (v ∘ u) ⊆ indices v := by
  rintro _ ⟨i,rfl⟩
  exact ⟨u i,rfl⟩

abbrev firstNormal {n : ℕ} (v : Fin (n+1) → Fin 5) :=
  normal G (indices v) (v 0) (Set.mem_range_self _)

@[simp] theorem firstNormal_f {n : ℕ} (v : Fin (n+1) → Fin 5) :
    firstNormal G v (f G (indices v)) = 1 := normal_f _ _ _ _

variable {s t u : Set (Fin 5)}

theorem denominators_mono (h : s ⊆ t) : denominators G s ≤ denominators G t :=
  Submonoid.closure_mono (Set.image_mono h)

def ambientMap (h : s ⊆ t) : Ambient G s →ₐ[k] Ambient G t :=
  IsLocalization.liftAlgHom (f := IsScalarTower.toAlgHom k (Poly k) (Ambient G t))
    (fun y : denominators G s => IsLocalization.map_units (Ambient G t)
      (⟨(y : Poly k),denominators_mono G h y.prop⟩ : denominators G t))

@[simp] theorem ambientMap_polynomial (h : s ⊆ t) (p : Poly k) :
    ambientMap G h (algebraMap (Poly k) (Ambient G s) p) = algebraMap (Poly k) (Ambient G t) p :=
  IsLocalization.lift_eq _ p

@[simp] theorem ambientMap_f (h : s ⊆ t) : ambientMap G h (f G s) = f G t :=
  ambientMap_polynomial G h G

@[simp] theorem ambientMap_coord (h : s ⊆ t) (i : Fin 5) :
    ambientMap G h (coord G s i) = coord G t i := ambientMap_polynomial G h (X i)

theorem ambientMap_comp (h : s ⊆ t) (l : t ⊆ u) :
    (ambientMap G l).comp (ambientMap G h) = ambientMap G (h.trans l) := by
  apply IsLocalization.algHom_ext (denominators G s)
  apply AlgHom.ext
  intro p
  change ambientMap G l (ambientMap G h (algebraMap (Poly k) _ p)) =
    ambientMap G (h.trans l) (algebraMap (Poly k) _ p)
  simp only [ambientMap_polynomial]

theorem ambientMap_id (s : Set (Fin 5)) : ambientMap G (Set.Subset.rfl : s ⊆ s) = AlgHom.id k _ := by
  apply IsLocalization.algHom_ext (denominators G s)
  apply AlgHom.ext
  intro p
  exact ambientMap_polynomial _ _ _

def divisorMap (h : s ⊆ t) : Divisor G s →ₐ[k] Divisor G t :=
  Ideal.Quotient.liftₐ _ ((π G t).comp (ambientMap G h)) ((Ideal.span_singleton_le_iff_mem _).mpr
    (show π G t (ambientMap G h (f G s)) = 0 by rw [ambientMap_f, π_f]))

@[simp] theorem divisorMap_π (h : s ⊆ t) (a : Ambient G s) :
    divisorMap G h (π G s a) = π G t (ambientMap G h a) := rfl

@[simp] theorem divisorMap_coord (h : s ⊆ t) (i : Fin 5) :
    divisorMap G h (π G s (coord G s i)) = π G t (coord G t i) := by
  rw [divisorMap_π, ambientMap_coord]

theorem restrict_square (h : s ⊆ t) :
    (π G t).comp (ambientMap G h) = (divisorMap G h).comp (π G s) := AlgHom.ext (fun _ => rfl)

theorem divisorMap_comp (h : s ⊆ t) (l : t ⊆ u) :
    (divisorMap G l).comp (divisorMap G h) = divisorMap G (h.trans l) := by
  apply Ideal.Quotient.algHom_ext k
  apply AlgHom.ext
  intro a
  change π G u (ambientMap G l (ambientMap G h a)) = π G u (ambientMap G (h.trans l) a)
  exact congrArg (π G u) (DFunLike.congr_fun (ambientMap_comp G h l) a)

theorem divisorMap_id (s : Set (Fin 5)) : divisorMap G (Set.Subset.rfl : s ⊆ s) = AlgHom.id k _ := by
  apply Ideal.Quotient.algHom_ext k
  apply AlgHom.ext
  intro a
  change π G s (ambientMap G (Set.Subset.rfl : s ⊆ s) a) = π G s a
  rw [ambientMap_id] <;> rfl

def complementMap (h : s ⊆ t) : Complement G s →ₐ[k] Complement G t :=
  IsLocalization.Away.liftAlgHom (f G s) (f := (cπ G t).comp (ambientMap G h)) (by
    rw [AlgHom.comp_apply, ambientMap_f]
    exact (fUnit_val G t) ▸ (fUnit G t).isUnit)

@[simp] theorem complementMap_cπ (h : s ⊆ t) (a : Ambient G s) :
    complementMap G h (cπ G s a) = cπ G t (ambientMap G h a) :=
  IsLocalization.Away.lift_eq _ _ _

theorem complementMap_comp (h : s ⊆ t) (l : t ⊆ u) :
    (complementMap G l).comp (complementMap G h) = complementMap G (h.trans l) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (f G s))
  apply AlgHom.ext
  intro a
  change complementMap G l (complementMap G h (cπ G s a)) = complementMap G (h.trans l) (cπ G s a)
  simp only [complementMap_cπ]
  exact congrArg (cπ G u) (DFunLike.congr_fun (ambientMap_comp G h l) a)

end CycleQ2GradientSimplex
end

#print axioms CycleQ2GradientSimplex.restrict_square
#print axioms CycleQ2GradientSimplex.divisorMap_comp
#print axioms CycleQ2GradientSimplex.complementBasis_apply
