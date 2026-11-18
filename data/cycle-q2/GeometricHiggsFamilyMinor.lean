import Proposal.GeometricHiggsSocle
import Proposal.GeometricHiggsCommutantOpen

/-!
# The scalar-commutant principal open of the full invariant sextic base

Apply the maximal commutant minor to the matrices constructed from the
universal Jacobian partials and the degree-eighteen trace row. At the original
Fermat coefficients it equals the fixed nonzero Fermat minor.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2HiggsFamilyMinor

open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2GeometricHiggsCommutantOpen
open CycleQ2HiggsSocle (H H_seed)

def parameter : CoeffRing := minor H

theorem seed_matrices : mapTuple seedEvaluation H = fermat := funext H_seed

theorem parameter_seed : seedEvaluation parameter = minor fermat := by
  rw [parameter, map_minor, seed_matrices]

theorem parameter_seed_ne_zero : seedEvaluation parameter ≠ 0 :=
  parameter_seed ▸ fermat_minor_ne_zero

theorem fermat_mem : fermatPoint ∈ PrimeSpectrum.basicOpen parameter := by
  apply (PrimeSpectrum.mem_basicOpen _ _).mpr
  exact parameter_seed_ne_zero

theorem scalar_on_fiber {K : Type*} [CommRing K] (φ : CoeffRing →+* K)
    (h : IsUnit (φ parameter)) (P : Matrix (Fin 33) (Fin 33) K)
    (he : ∀ m, P.transpose * (H m).map φ = (H m).map φ * P) :
    ∃ c : K, P = c • (1 : Matrix (Fin 33) (Fin 33) K) := by
  apply scalar_of_minor_isUnit (mapTuple φ H) _ P he
  exact map_minor φ H ▸ h

theorem projector_on_fiber {K : Type*} [CommRing K] [IsDomain K] (φ : CoeffRing →+* K)
    (h : IsUnit (φ parameter)) (P : Matrix (Fin 33) (Fin 33) K)
    (he : ∀ m, P.transpose * (H m).map φ = (H m).map φ * P) (hid : P * P = P) :
    P = 0 ∨ P = 1 := by
  apply projector_trivial_of_minor_isUnit (mapTuple φ H) _ P he hid
  exact map_minor φ H ▸ h

end CycleQ2HiggsFamilyMinor
end

#print axioms CycleQ2HiggsFamilyMinor.fermat_mem
#print axioms CycleQ2HiggsFamilyMinor.projector_on_fiber
