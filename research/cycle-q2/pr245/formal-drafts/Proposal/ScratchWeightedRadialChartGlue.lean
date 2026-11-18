import Proposal.ScratchWeightedHorizontalChartGlue
import Proposal.ScratchWeightedRadialExpansion
import Proposal.ScratchLogInteriorAnti

/-!
# The actual chart pullbacks of an Euler-contracted form agree

A homogeneous cone form of weight zero gives a horizontal form by Euler
insertion. The insertion preserves the complementary weight of every finite
coordinate term, so its pullbacks to the two normalized chart slices agree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2WeightedRadialChartGlue

open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2WeightedChartShear (exteriorWeight coordWedge)
open CycleQ2WeightedRadialExpansion (radialCoefficient radialCoefficient_scale interior_finite_expansion)
open CycleQ2WeightedHorizontalChartGlue (horizontal_chart_change)
open CycleQ2HodgeEulerContractionRestriction (pull)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open scoped KaehlerDifferential

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

theorem radial_chart_change (π σ : R →ₐ[k] S)
    (l : Ω[R⁄k] →ₗ[R] R) (t u : S) (ht : t*u=1) (x : Fin 5 → R)
    (hσ : ∀ j, σ (x j) = t^(geometricWeight j)*π (x j))
    (hl : ∀ j, l (KaehlerDifferential.D k R (x j)) = (geometricWeight j:R)*x j)
    {A : Type} (s : Finset A) (n : ℕ) (I : A → Fin (n+2) → Fin 5) (c : A → R)
    (hc : ∀ a ∈ s, σ (c a)*t^(exteriorWeight (I a)) = π (c a)) :
    pull σ (n+1) (interior (n+1) l (∑ a ∈ s, c a • coordWedge (k := k) x (I a))) =
      pull π (n+1) (interior (n+1) l (∑ a ∈ s, c a • coordWedge (k := k) x (I a))) := by
  classical
  have he := interior_finite_expansion l x hl s (n+1) I c
  rw [he]
  apply horizontal_chart_change π σ l t u ht x hσ hl (s.product Finset.univ) n
    (fun p => p.2.removeNth (I p.1)) (fun p => radialCoefficient x (c p.1) (I p.1) p.2)
  · intro p hp
    exact radialCoefficient_scale π.toRingHom σ.toRingHom x t hσ (I p.1) (c p.1)
      (hc p.1 (Finset.mem_product.mp hp).1) p.2
  · rw [← he]
    exact CycleQ2LogInteriorAnti.interior_square n l _

end CycleQ2WeightedRadialChartGlue
end

#print axioms CycleQ2WeightedRadialChartGlue.radial_chart_change
