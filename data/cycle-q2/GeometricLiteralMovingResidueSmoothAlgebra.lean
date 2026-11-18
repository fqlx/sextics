import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The smooth hypersurface adjunction map in relative dimension one

In a two-element basis of ambient Kähler differentials, wedging with the
equation differential is its two-by-two determinant. If the two partial
derivatives generate the unit ideal on the hypersurface, this determinant
identifies its ordinary Kähler module with its canonical numerator line.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LiteralMovingResidueSmoothAlgebra

section Determinant
variable {C M : Type*} [CommRing C] [AddCommGroup M] [Module C M]

/-- If a conormal vector is unimodular, the determinant with that vector
trivializes the quotient by the conormal relation. -/
theorem determinant_bijective (x y : M) (a b : C)
    (gen : ∀ z : M, ∃ m n : C, z = m • x + n • y)
    (rel : a • x + b • y = 0) (smooth : IsCoprime a b)
    (F : M →ₗ[C] C) (Fx : F x = -b) (Fy : F y = a) : Function.Bijective F := by
  obtain ⟨c,d,hu⟩ := smooth
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨m,n,rfl⟩ := gen z
    have hdet : -m*b+n*a=0 := by simpa [Fx, Fy] using hz
    let s := m*c+n*d
    have hm : m = s*a := by dsimp [s]; linear_combination -m * hu - d * hdet
    have hn : n = s*b := by dsimp [s]; linear_combination -n * hu + c * hdet
    calc
      m • x + n • y = (s*a) • x + (s*b) • y :=
        congrArg₂ (· + ·) (congrArg (· • x) hm) (congrArg (· • y) hn)
      _ = s • (a • x+b • y) := by rw [smul_add, smul_smul, smul_smul]
      _ = 0 := by rw [rel, smul_zero]
  · intro z
    refine ⟨z • ((-d) • x + c • y), ?_⟩
    simp only [map_smul, map_add, Fx, Fy, smul_eq_mul, neg_mul_neg]
    rw [add_comm, hu, mul_one]

end Determinant

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] (e : A)

private abbrev I := Ideal.span {e}
private abbrev C := A ⧸ I e
private abbrev q := Ideal.Quotient.mk (I e)
private abbrev κ := KaehlerDifferential.map K K A (C e)

variable (basis : KaehlerDifferential K A ≃ₗ[A] A × A)
private abbrev dx := basis (KaehlerDifferential.D K A e)

/-- The actual Kähler map for a principal quotient is bijective when its
coordinate formula is the conormal determinant and its partials are coprime
after reduction modulo the equation. -/
theorem quotientAdjunction_bijective (F : KaehlerDifferential K (C e) →ₗ[C e] C e)
    (hF : ∀ ω : KaehlerDifferential K A,
      F (κ (K := K) e ω) = q e ((dx e basis).1 * (basis ω).2 - (dx e basis).2 * (basis ω).1))
    (smooth : IsCoprime (q e (dx e basis).1) (q e (dx e basis).2)) :
    Function.Bijective F := by
  let x := basis.symm (1,0)
  let y := basis.symm (0,1)
  have expand (ω : KaehlerDifferential K A) :
      κ (K := K) e ω = q e (basis ω).1 • κ (K := K) e x + q e (basis ω).2 • κ (K := K) e y := by
    have h : ω = (basis ω).1 • x + (basis ω).2 • y := by
      apply basis.injective
      simp [x, y, Prod.smul_mk]
    exact (congrArg (κ (K := K) e) h).trans (by rw [map_add, map_smul, map_smul]; rfl)
  apply determinant_bijective (κ (K := K) e x) (κ (K := K) e y)
    (q e (dx e basis).1) (q e (dx e basis).2) _ _ smooth F
  · simp [x, hF]
  · simp [y, hF]
  · intro z
    obtain ⟨ω,rfl⟩ := KaehlerDifferential.map_surjective_of_surjective K K A (C e)
      (Ideal.Quotient.mk_surjective) z
    exact ⟨_, _, expand ω⟩
  · rw [← expand]
    change KaehlerDifferential.map K K A (C e) (KaehlerDifferential.D K A e) = 0
    rw [KaehlerDifferential.map_D]
    have he : (algebraMap A (C e)) e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [he, map_zero]

section Line
open scoped Pointwise
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Reduce the chosen trivialization of the numerator line along the
hypersurface quotient. -/
def quotientLine (E : M ≃ₗ[A] A) :
    (M ⧸ (I e • (⊤ : Submodule A M))) ≃ₗ[C e] C e := by
  let L : (M ⧸ (I e • (⊤ : Submodule A M))) ≃ₗ[A] C e :=
    Submodule.Quotient.equiv _ (I e) E (by
      rw [Submodule.map_smul'', Submodule.map_top, E.range]
      exact Ideal.mul_top _)
  exact
    { __ := L
      map_smul' := by
        intro a x
        obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨v,rfl⟩ := (I e • (⊤ : Submodule A M)).mkQ_surjective x
        change q e (E (r • v)) = q e r * q e (E v)
        rw [E.map_smul, smul_eq_mul, map_mul] }

theorem quotientLine_mk (E : M ≃ₗ[A] A) (m : M) :
    quotientLine e E ((I e • (⊤ : Submodule A M)).mkQ m) = q e (E m) := rfl

end Line
end CycleQ2LiteralMovingResidueSmoothAlgebra
end

#print axioms CycleQ2LiteralMovingResidueSmoothAlgebra.quotientAdjunction_bijective
