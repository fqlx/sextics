import Proposal.GeometricGradientSimplex
import Proposal.GeometricConeGradientBasis

/-! Exact differential frames on the cone hypersurface over the gradient nerve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GradientSimplex
variable {k : Type} [CommRing k] (G : Poly k)
open MvPolynomial CycleQ2WeightedCechPresentations (denominators derivative_mem)

abbrev divisorBasis (s : Set (Fin 5)) (i : Fin 5) (hi : i ∈ s) :
    Module.Basis (Fin 4) (Divisor G s) (KaehlerDifferential k (Divisor G s)) :=
  CycleQ2ConeGradientBasis.basis (denominators G s) G i (derivative_mem G hi)

@[simp] theorem divisorBasis_apply (s : Set (Fin 5)) (i : Fin 5) (hi : i ∈ s) (j : Fin 4) :
    divisorBasis G s i hi j = KaehlerDifferential.D k _ (π G s (coord G s (i.succAbove j))) :=
  CycleQ2ConeGradientBasis.basis_apply _ _ _ _ j

abbrev firstBasis {n : ℕ} (v : Fin (n+1) → Fin 5) :=
  divisorBasis G (indices v) (v 0) (Set.mem_range_self _)

@[simp] theorem firstBasis_apply {n : ℕ} (v : Fin (n+1) → Fin 5) (j : Fin 4) :
    firstBasis G v j = KaehlerDifferential.D k _
      (π G (indices v) (coord G (indices v) ((v 0).succAbove j))) :=
  divisorBasis_apply _ _ _ _ _

end CycleQ2GradientSimplex
end

#print axioms CycleQ2GradientSimplex.firstBasis_apply
