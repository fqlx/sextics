import Proposal.ScratchWeightedNormalTaylor
import Proposal.ScratchFormalNormalSeries
import Proposal.GeometricMonicWeightedPrimitiveIdentity

/-!
# The cubic-pole residue on the normal chart of a weighted threefold

Translate the first spatial coordinate at a point of the hypersurface and
keep the other coordinates fixed. This computes the coefficient of exponent
minus one in the Laurent expansion of the original rational pole, using
the actual normal derivatives of the chart polynomial and its numerator.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedNormalResidue

open MvPolynomial CycleQ2WeightedNormalTaylor CycleQ2FormalNormalSeries
variable {A K : Type*} [CommRing A] [Field K] [CharZero K]
variable (v : Pol A →+* K) (f q : Pol A)

/-- Coefficient of the volume after translating the rational function q/f³
at the given point. -/
def meromorphic : LaurentSeries K :=
  algebraMap (Polynomial K) (LaurentSeries K) (translate v q) /
    (algebraMap (Polynomial K) (LaurentSeries K) (translate v f)) ^ 3

theorem meromorphic_coeff_neg_one (hf : v f = 0) (hg : v (pderiv 0 f) ≠ 0) :
    (meromorphic v f q).coeff (-1) =
      SplitHigherResidue.normalSourceTwo (v q) (v (pderiv 0 q)) (v (pderiv 0 (pderiv 0 q)))
        (v (pderiv 0 f)) (v (pderiv 0 (pderiv 0 f))) (v (pderiv 0 (pderiv 0 (pderiv 0 f)))) /
        v (pderiv 0 f) := by
  let a := translate v q
  let u := (translate v f).divX
  obtain ⟨h₀, h₁, h₂⟩ := normal_unit_jets v f
  have hu : PowerSeries.constantCoeff (u : PowerSeries K) ≠ 0 := by
    simpa only [u, Polynomial.constantCoeff_coe, h₀] using hg
  have he : meromorphic v f q = cubicPole (a : PowerSeries K) (u : PowerSeries K) := by
    unfold meromorphic
    rw [translate_equation v f hf]
    simp only [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_mul, Polynomial.coe_X, cubicPole, a, u]
  rw [he, cubicPole_residue_eq_normalSourceTwo _ _ hu]
  simp only [a, u, Polynomial.constantCoeff_coe, Polynomial.coeff_coe, translate_coeff_zero,
    translate_coeff_one, translate_coeff_two, h₀, h₁, h₂]
  congr 2 <;> ring

/-- The undecomposed weighted numerator on z₀=1 yields exactly the density
used by the cleared three-variable divergence equation. -/
theorem weighted_residue_eq_density (hf : v f = 0) (hg : v (pderiv 0 f) ≠ 0) :
    (meromorphic v f CycleQ2MonicWeightedPrimitiveIdentity.b).coeff (-1) =
      CycleQ2MonicWeightedPrimitiveIdentity.density v f :=
  meromorphic_coeff_neg_one v f _ hf hg

end CycleQ2WeightedNormalResidue
end
#print axioms CycleQ2WeightedNormalResidue.weighted_residue_eq_density
