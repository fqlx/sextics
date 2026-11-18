import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Algebra.Tower

/-! Elimination of a coordinate with a unit coefficient from a cotangent frame. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2OmittedCoordinateBasis
open Module

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] {n : ℕ} (b : Basis (Fin (n+1)) R M) (π : M →ₗ[R] N)
  (hπ : Function.Surjective π) (f : M) (hf : π f = 0)
  (i : Fin (n+1)) (u : Rˣ) (hu : b.repr f i = (u : R))

include hπ hf hu

/-- A relation with a unit coefficient at i lets one eliminate that coordinate
from every lift of a quotient-module element. -/
theorem span_omitted : ⊤ ≤ Submodule.span S (Set.range (fun j => π (b (i.succAbove j)))) := by
  intro z _
  obtain ⟨w,rfl⟩ := hπ z
  let y := w - (b.repr w i * (↑u⁻¹ : R)) • f
  have hy : b.repr y i = 0 := by
    simp only [y, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
      hu, mul_assoc, u.inv_mul, mul_one, sub_self]
  have he := b.sum_repr y
  rw [Fin.sum_univ_succAbove _ i, hy, zero_smul, zero_add] at he
  have hp : π y = π w := by simp only [y, map_sub, map_smul, hf, smul_zero, sub_zero]
  rw [← hp, ← he, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul, ← IsScalarTower.algebraMap_smul S]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

/-- The remaining coordinates are a basis once dual functionals read their entries. -/
def basis (l : Fin n → N →ₗ[S] S)
    (hl : ∀ j q, l j (π (b (i.succAbove q))) = if q = j then 1 else 0) :
    Basis (Fin n) S N :=
  Basis.mk (by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := congrArg (l j) hc
    simpa [map_sum, map_smul, hl, smul_eq_mul, mul_ite] using h)
    (span_omitted b π hπ f hf i u hu)

@[simp] theorem basis_apply (l : Fin n → N →ₗ[S] S)
    (hl : ∀ j q, l j (π (b (i.succAbove q))) = if q = j then 1 else 0) (j : Fin n) :
    basis b π hπ f hf i u hu l hl j = π (b (i.succAbove j)) :=
  Basis.mk_apply _ _ _

end CycleQ2OmittedCoordinateBasis
end
#print axioms CycleQ2OmittedCoordinateBasis.basis
