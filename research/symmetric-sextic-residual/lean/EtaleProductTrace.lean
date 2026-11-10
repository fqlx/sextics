import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.IntermediateField.Basic

noncomputable section
open scoped BigOperators
namespace EtaleProductTrace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K]
variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  [∀ i, FiniteDimensional K (F i)]

/-- The regular trace of a finite product is the sum of its factor traces. -/
theorem trace_single (i : ι) (a : F i) :
    Algebra.trace K (∀ j, F j) (Pi.single i a) = Algebra.trace K (F i) a := by
  rw [Algebra.trace_apply, Algebra.trace_apply]
  have hm : Algebra.lmul K (∀ j, F j) (Pi.single i a) =
      (LinearMap.single K F i).comp ((Algebra.lmul K (F i) a).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro x
    funext j
    change (Pi.single i a j)*x j = Pi.single i (a*x i) j
    by_cases h : j = i
    · subst j
      simp
    · simp [Pi.single_apply, h, Ne.symm h]
  rw [hm, LinearMap.trace_comp_comm']
  simp [LinearMap.comp_assoc, LinearMap.proj_comp_single_same]

theorem trace_pi (x : ∀ i, F i) :
    Algebra.trace K (∀ i, F i) x = ∑ i, Algebra.trace K (F i) (x i) := by
  calc
    Algebra.trace K (∀ i, F i) x = Algebra.trace K (∀ i, F i) (∑ i, Pi.single i (x i)) := by
      rw [LinearMap.sum_single_apply F x]
    _ = ∑ i, Algebra.trace K (F i) (x i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => trace_single (K := K) F i (x i))


/-- The product algebra's regular trace divided by its dimension is the
ordinary sum of the factor traces divided by the sum of their dimensions. -/
theorem normalized_trace_pi (x : ∀ i, F i) :
    ((Module.finrank K (∀ i, F i) : ℕ) : K)⁻¹ * Algebra.trace K (∀ i, F i) x =
      (∑ i, ((Module.finrank K (F i) : ℕ) : K))⁻¹ *
        ∑ i, Algebra.trace K (F i) (x i) := by
  rw [trace_pi F, Module.finrank_pi_fintype]
  simp only [Nat.cast_sum]


/-- Transport from any concrete finite algebra through an explicit algebra
isomorphism to its field factors. The isomorphism is an input, not constructed. -/
theorem trace_of_algEquiv {A : Type*} [CommRing A] [Algebra K A]
    (e : A ≃ₐ[K] (∀ i, F i)) (x : A) :
    Algebra.trace K A x = ∑ i, Algebra.trace K (F i) (e x i) := by
  rw [← Algebra.trace_eq_of_algEquiv e x, trace_pi F]

end EtaleProductTrace
#print axioms EtaleProductTrace.trace_pi

#print axioms EtaleProductTrace.normalized_trace_pi

#print axioms EtaleProductTrace.trace_of_algEquiv
