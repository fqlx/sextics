import Proposal.ScratchWeightedNormalCofactor
import Proposal.ScratchWeightedLocalPresentations

/-!
# Homogeneous polynomial certificates for every ordinary residue coefficient

The selected gradient is an invertible homogeneous polynomial on its actual
patch. Its reciprocal therefore has an explicit homogeneous fraction
presentation, with polynomial numerator one and denominator the gradient.
The same presentation is preserved by the quotient to the divisor.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2WeightedNormalCofactor
open MvPolynomial
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2PoleReductionGradient (Poly)
open CycleQ2WeightedChartShear (exteriorWeight)
open CycleQ2WeightedRadialExpansion (insertedCoefficient exteriorWeight_remove)
open CycleQ2WeightedLocalPresentations (Represented integer_degree)

variable {k T : Type} [CommRing k] [CommRing T] [Algebra k T]
variable (M : Submonoid (Poly k))
local notation "B" => Localization M
local notation "ι" => algebraMap (Poly k) B

theorem inverseGradient_represented (G : Poly k) (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (i : Fin 5) (hi : pderiv i G ∈ M) :
    Represented ι M (-(↑(6-geometricWeight i : ℕ) : ℤ)) (inverseGradient M G i hi) := by
  refine ⟨1,pderiv i G,0,(6-geometricWeight i : ℕ),isWeightedHomogeneous_one _ _,
    integer_degree (CycleQ2IncidenceChartMinor.pderiv_homogeneous hG i),hi,by simp,?_⟩
  rw [map_one,mul_comm,gradient_mul_inverse]

/-- The finite expansion of the ordinary residue gives, term-by-term,
homogeneous fraction certificates of the opposite degrees to its wedges. -/
theorem gradient_residue_represented (q : B →ₐ[k] T)
    (G : Poly k) (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (i : Fin 5) (hi : pderiv i G ∈ M) {n : ℕ} (I : Fin (n+1) → Fin 5) (c : B)
    (hc : Represented ι M (6 - (exteriorWeight I : ℤ)) c) (j : Fin (n+1)) :
    Represented (q.toRingHom.comp ι) M (-(exteriorWeight (j.removeNth I) : ℤ))
      (q (insertedCoefficient (normalValue i (inverseGradient M G i hi)) c I j)) := by
  suffices h : Represented ι M (-(exteriorWeight (j.removeNth I) : ℤ))
      (insertedCoefficient (normalValue i (inverseGradient M G i hi)) c I j) from h.map q.toRingHom
  by_cases hji : I j = i
  · rw [insertedCoefficient,normalValue,if_pos hji]
    have hs : Represented ι M 0 ((-1 : B)^j.val) := by
      simpa only [map_pow,map_neg,map_one] using Represented.constant ι M ((-1 : k)^j.val)
    have h := hc.mul (hs.mul (inverseGradient_represented M G hG i hi))
    have hw := exteriorWeight_remove I j
    rw [hji] at hw
    have hiw := CycleQ2IncidenceChartMinor.geometricWeight_le_two i
    convert h using 1 <;> omega
  · simp only [insertedCoefficient,normalValue,if_neg hji,mul_zero]
    exact Represented.zero _ _ _

end CycleQ2WeightedNormalCofactor
end
#print axioms CycleQ2WeightedNormalCofactor.gradient_residue_represented
