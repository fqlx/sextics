import Proposal.GeometricHiggsFamilyMultiplication
import Proposal.GeometricHiggsPairedProjectors
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# No proper compatible graded projector over the full-family open

The genuine degree-six and degree-twelve character-one components of the
specialized Jacobian ring carry the trace pairing and the degree-six
multiplication maps. Their coordinate matrices are the universal
socle-trace matrices. The common Fermat-open determinant forces every
compatible graded idempotent on their direct sum to be zero or identity.
This algebraic statement concerns the Jacobian rings of the full family;
comparison with geometric variations of Hodge structure is separate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HiggsFamilyGrading

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHiggsCommutantOpen (minor mapTuple map_minor)
open CycleQ2HiggsPairedProjectors (PreservesGrading totalHiggs)

variable {K : Type} [Field K] (φ : CoeffRing →+* K)

theorem actual_tuple (h : φ parameter ≠ 0) :
    CycleQ2HiggsPairedProjectors.tuple (upperBasis φ h) (pairing φ) (higgs φ) (tangentBasis φ h) =
      mapTuple φ CycleQ2HiggsSocle.H := by
  funext m
  ext i j
  exact (CycleQ2HiggsPairedProjectors.tuple_apply _ _ _ _ m i j).trans
    (higgs_basis_entry φ h m i j)

theorem compatible_scalar (h : φ parameter ≠ 0)
    (E : Module.End K (Upper φ × Lower φ)) (hg : PreservesGrading E)
    (hself : ∀ x y, CycleQ2HiggsPairedProjectors.pairing (pairing φ) (E x) y =
      CycleQ2HiggsPairedProjectors.pairing (pairing φ) x (E y))
    (hc : ∀ t : Tangent φ, E * totalHiggs (higgs φ t) = totalHiggs (higgs φ t) * E) :
    ∃ c : K, E = c • 1 := by
  apply CycleQ2HiggsPairedProjectors.compatible_scalar_of_minor_isUnit
    (upperBasis φ h) (pairing φ) (higgs φ) (tangentBasis φ h) (pairing_flip_injective φ h) _ E hg hself hc
  rw [actual_tuple, ← map_minor]
  exact isUnit_iff_ne_zero.mpr (factor_conditions φ h).2.2.2.2

theorem compatible_projector_trivial (h : φ parameter ≠ 0)
    (E : Module.End K (Upper φ × Lower φ)) (hg : PreservesGrading E)
    (hself : ∀ x y, CycleQ2HiggsPairedProjectors.pairing (pairing φ) (E x) y =
      CycleQ2HiggsPairedProjectors.pairing (pairing φ) x (E y))
    (hc : ∀ t : Tangent φ, E * totalHiggs (higgs φ t) = totalHiggs (higgs φ t) * E)
    (hi : E * E = E) : E = 0 ∨ E = 1 := by
  apply CycleQ2HiggsPairedProjectors.compatible_projector_trivial_of_minor_isUnit
    (upperBasis φ h) (pairing φ) (higgs φ) (tangentBasis φ h) (pairing_flip_injective φ h) _ E hg hself hc hi
  rw [actual_tuple, ← map_minor]
  exact isUnit_iff_ne_zero.mpr (factor_conditions φ h).2.2.2.2

/-- The field of every scheme point of the exhibited principal open
satisfies the same projector conclusion. -/
theorem compatible_projector_trivial_at (p : PrimeSpectrum CoeffRing)
    (hp : p ∈ PrimeSpectrum.basicOpen parameter)
    (E : Module.End p.asIdeal.ResidueField
      (Upper (algebraMap CoeffRing p.asIdeal.ResidueField) ×
       Lower (algebraMap CoeffRing p.asIdeal.ResidueField))) (hg : PreservesGrading E)
    (hself : ∀ x y, CycleQ2HiggsPairedProjectors.pairing
      (pairing (algebraMap CoeffRing p.asIdeal.ResidueField)) (E x) y =
      CycleQ2HiggsPairedProjectors.pairing
      (pairing (algebraMap CoeffRing p.asIdeal.ResidueField)) x (E y))
    (hc : ∀ t, E * totalHiggs (higgs (algebraMap CoeffRing p.asIdeal.ResidueField) t) =
      totalHiggs (higgs (algebraMap CoeffRing p.asIdeal.ResidueField) t) * E)
    (hi : E * E = E) : E = 0 ∨ E = 1 := by
  apply compatible_projector_trivial _ _ E hg hself hc hi
  exact fun hz => (PrimeSpectrum.mem_basicOpen parameter p).mp hp
    (Ideal.algebraMap_residueField_eq_zero.mp hz)

end CycleQ2HiggsFamilyGrading
end

#print axioms CycleQ2HiggsFamilyGrading.compatible_scalar
#print axioms CycleQ2HiggsFamilyGrading.compatible_projector_trivial_at
