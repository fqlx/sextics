import Proposal.ScratchWeightedChartShear
import Proposal.GeometricExteriorRankOne
import Proposal.GeometricHodgeEulerContractionRestriction
import Proposal.GeometricHodgeEulerOverlapBinding

/-! Horizontal forms of degree zero agree on projective chart overlaps. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedHorizontalChartGlue
open CycleQ2WeightedChartShear
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2HodgeEulerContractionRestriction (pull pullOne pullOne_D)
open CycleQ2GeometricExteriorSheaf (exteriorMap)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open scoped KaehlerDifferential

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- The two true pullbacks along changes of weighted section coincide on the finite
expansion of a horizontal form when each coefficient has complementary weight. -/
theorem horizontal_chart_change (π σ : R →ₐ[k] S)
    (l : Ω[R⁄k] →ₗ[R] R) (t u : S) (ht : t*u=1) (x : Fin 5 → R)
    (hσ : ∀ j, σ (x j) = t^(geometricWeight j)*π (x j))
    (hl : ∀ j, l (KaehlerDifferential.D k R (x j)) = (geometricWeight j:R)*x j)
    {ι : Type} (s : Finset ι) (n : ℕ) (I : ι → Fin (n+1) → Fin 5) (c : ι → R)
    (hc : ∀ a ∈ s, σ (c a)*t^(exteriorWeight (I a)) = π (c a))
    (hω : interior n l (∑ a ∈ s, c a • coordWedge (k := k) x (I a)) = 0) :
    pull σ (n+1) (∑ a ∈ s, c a • coordWedge (k := k) x (I a)) =
      pull π (n+1) (∑ a ∈ s, c a • coordWedge (k := k) x (I a)) := by
  let F := frozen σ (pullOne σ) l t u
  refine (CycleQ2ExteriorRankOne.exteriorMap_horizontal σ.toRingHom F (pullOne σ)
    (u • KaehlerDifferential.D k S t) l (moving_eq_frozen σ (pullOne σ) l t u) n _ hω).trans ?_
  exact frozen_sum π σ (pullOne σ) l t u (pullOne π) ht x hσ
    (fun j => pullOne_D σ _) (fun j => pullOne_D π _) hl s I c hc

end CycleQ2WeightedHorizontalChartGlue
end
#print axioms CycleQ2WeightedHorizontalChartGlue.horizontal_chart_change
