import Proposal.ScratchWeightedChartShear
import Proposal.GeometricLiteralThreefoldResidueContraction

/-!
# Radial insertion preserves the weight of a finite coordinate expansion

Inserting the weighted Euler vector removes one differential dXᵢ and
multiplies its coefficient by the signed value wᵢXᵢ. The lost exterior
weight is exactly the gained coefficient weight on a chart transition.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2WeightedRadialExpansion

open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2WeightedChartShear (coordWedge exteriorWeight)
open CycleQ2LiteralThreefoldResidueContraction (interior interior_wedge)
open scoped KaehlerDifferential

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R]

/-- Signed cofactor of an arbitrary insertion in spatial coordinates. -/
def insertedCoefficient {n : ℕ} (v : Fin 5 → R) (c : R) (I : Fin (n+1) → Fin 5)
    (j : Fin (n+1)) : R :=
  c * ((-1 : R) ^ j.val * v (I j))

def radialCoefficient {n : ℕ} (x : Fin 5 → R) (c : R) (I : Fin (n+1) → Fin 5)
    (j : Fin (n+1)) : R :=
  insertedCoefficient (fun i => (geometricWeight i : R) * x i) c I j

theorem exteriorWeight_remove {n : ℕ} (I : Fin (n+1) → Fin 5) (j : Fin (n+1)) :
    exteriorWeight I = geometricWeight (I j) + exteriorWeight (j.removeNth I) :=
  Fin.sum_univ_succAbove (fun i => geometricWeight (I i)) j

theorem interior_coordWedge_with (l : Ω[R⁄k] →ₗ[R] R) (x v : Fin 5 → R)
    (hl : ∀ i, l (KaehlerDifferential.D k R (x i)) = v i)
    (n : ℕ) (I : Fin (n+1) → Fin 5) (c : R) :
    interior n l (c • coordWedge (k := k) x I) =
      ∑ j : Fin (n+1), insertedCoefficient v c I j • coordWedge (k := k) x (j.removeNth I) := by
  rw [map_smul, coordWedge, interior_wedge, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hl, ← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one,
    smul_smul, mul_assoc, insertedCoefficient, coordWedge] <;> rfl

theorem interior_expansion_with (l : Ω[R⁄k] →ₗ[R] R) (x v : Fin 5 → R)
    (hl : ∀ i, l (KaehlerDifferential.D k R (x i)) = v i)
    {A : Type} (s : Finset A) (n : ℕ) (I : A → Fin (n+1) → Fin 5) (c : A → R) :
    interior n l (∑ a ∈ s, c a • coordWedge (k := k) x (I a)) =
      ∑ p ∈ s.product (Finset.univ : Finset (Fin (n+1))),
        insertedCoefficient v (c p.1) (I p.1) p.2 •
          coordWedge (k := k) x (p.2.removeNth (I p.1)) := by
  rw [map_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  exact interior_coordWedge_with l x v hl n (I a) (c a)

theorem interior_coordWedge (l : Ω[R⁄k] →ₗ[R] R) (x : Fin 5 → R)
    (hl : ∀ i, l (KaehlerDifferential.D k R (x i)) = (geometricWeight i : R) * x i)
    (n : ℕ) (I : Fin (n+1) → Fin 5) (c : R) :
    interior n l (c • coordWedge (k := k) x I) =
      ∑ j : Fin (n+1), radialCoefficient x c I j • coordWedge (k := k) x (j.removeNth I) :=
  interior_coordWedge_with l x _ hl n I c

theorem interior_finite_expansion (l : Ω[R⁄k] →ₗ[R] R) (x : Fin 5 → R)
    (hl : ∀ i, l (KaehlerDifferential.D k R (x i)) = (geometricWeight i : R) * x i)
    {A : Type} (s : Finset A) (n : ℕ) (I : A → Fin (n+1) → Fin 5) (c : A → R) :
    interior n l (∑ a ∈ s, c a • coordWedge (k := k) x (I a)) =
      ∑ p ∈ s.product (Finset.univ : Finset (Fin (n+1))),
        radialCoefficient x (c p.1) (I p.1) p.2 •
          coordWedge (k := k) x (p.2.removeNth (I p.1)) :=
  interior_expansion_with l x _ hl s n I c

/-- The transition factor for a coefficient compensates the weight of its
remaining differentials after insertion of the radial field. -/
theorem radialCoefficient_scale (π σ : R →+* S) (x : Fin 5 → R) (t : S)
    (hσ : ∀ i, σ (x i) = t^(geometricWeight i) * π (x i))
    {n : ℕ} (I : Fin (n+1) → Fin 5) (c : R)
    (hc : σ c * t^(exteriorWeight I) = π c) (j : Fin (n+1)) :
    σ (radialCoefficient x c I j) * t^(exteriorWeight (j.removeNth I)) =
      π (radialCoefficient x c I j) := by
  rw [exteriorWeight_remove I j, pow_add] at hc
  simp only [radialCoefficient,insertedCoefficient,map_mul,map_pow,map_neg,map_one,map_natCast,hσ]
  linear_combination ((-1:S)^j.val * ((geometricWeight (I j):S) * π (x (I j)))) * hc

end CycleQ2WeightedRadialExpansion
end

#print axioms CycleQ2WeightedRadialExpansion.interior_finite_expansion
#print axioms CycleQ2WeightedRadialExpansion.radialCoefficient_scale
