import Proposal.ScratchWeightedLocalPresentations
import Proposal.ScratchWeightedRadialExpansion
import Proposal.GeometricConeSimplexCofactor

/-!
# Homogeneous coordinate expansions for signed cone cofactors

The degree-six ambient logarithmic numerators are finite sums of coordinate
wedges with homogeneous localized coefficients. A coordinate contraction
removes the corresponding weight. The sparse formula also handles repeated
coordinates, vanishing terms, and all signs of the complementary minors.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedCofactorExpansions
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2WeightedLocalPresentations (Poly Represented)
open CycleQ2WeightedChartShear (coordWedge exteriorWeight)
open CycleQ2WeightedRadialExpansion (exteriorWeight_remove insertedCoefficient interior_expansion_with)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2ConeSimplexCofactor (Frame volume top flux biv)
open scoped KaehlerDifferential

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable (v : Poly k →+* R) (M : Submonoid (Poly k)) (x : Fin 5 → R)

/-- Expansion before residue, allowing any total weight and the original
ambient ring. -/
structure WeightedExpansion (d : ℤ) (n : ℕ) (ω : ⋀[R]^n Ω[R⁄k]) where
  index : Type
  terms : Finset index
  wedge : index → Fin n → Fin 5
  coefficient : index → R
  formula : ω = ∑ a ∈ terms, coefficient a • coordWedge (k := k) x (wedge a)
  homogeneous : ∀ a ∈ terms,
    Represented v M (d - (exteriorWeight (wedge a) : ℤ)) (coefficient a)

namespace WeightedExpansion
variable {v M x} {d : ℤ} {n : ℕ}

def zero : WeightedExpansion v M x d n 0 where
  index := Unit
  terms := ∅
  wedge := fun _ _ => 0
  coefficient := fun _ => 0
  formula := by simp
  homogeneous := by simp

def sum {A : Type} (s : Finset A) (ω : A → ⋀[R]^n Ω[R⁄k])
    (e : ∀ a, WeightedExpansion v M x d n (ω a)) :
    WeightedExpansion v M x d n (∑ a ∈ s, ω a) where
  index := Σ a, (e a).index
  terms := s.sigma (fun a => (e a).terms)
  wedge := fun p => (e p.1).wedge p.2
  coefficient := fun p => (e p.1).coefficient p.2
  formula := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun a _ => (e a).formula
  homogeneous := fun p hp => (e p.1).homogeneous p.2 (Finset.mem_sigma.mp hp).2

private theorem sign_represented (v : Poly k →+* R) (M : Submonoid (Poly k)) (r : ℕ) :
    Represented v M 0 ((-1 : R)^r) := by
  simpa only [map_pow,map_neg,map_one] using Represented.constant v M ((-1:k)^r)

private theorem sparse_term {l : ℕ} (I : Fin (l+1) → Fin 5) (i : Fin 5)
    (j : Fin (l+1)) {c : R} (hc : Represented v M (d - (exteriorWeight I : ℤ)) c) :
    Represented v M (d - (geometricWeight i : ℤ) - (exteriorWeight (j.removeNth I) : ℤ))
      (insertedCoefficient (fun a => if a = i then 1 else 0) c I j) := by
  by_cases h : I j = i
  · rw [insertedCoefficient, if_pos h, mul_one]
    have hdeg := exteriorWeight_remove I j
    rw [h] at hdeg
    have hs := hc.mul (sign_represented v M j.val)
    convert hs using 1 <;> omega
  · simp only [insertedCoefficient,if_neg h,mul_zero]
    exact Represented.zero _ _ _

/-- The strict coordinate contraction lowers the total degree by that of its
selected coordinate. All vanishing terms retain a homogeneous zero presentation. -/
def contract {ω : ⋀[R]^(n+1) Ω[R⁄k]} (e : WeightedExpansion v M x d (n+1) ω)
    (b : Frame k R) (hb : ∀ i, b i = KaehlerDifferential.D k R (x i)) (i : Fin 5) :
    WeightedExpansion v M x (d - (geometricWeight i : ℤ)) n (interior n (b.coord i) ω) where
  index := e.index × Fin (n+1)
  terms := e.terms.product Finset.univ
  wedge := fun p => p.2.removeNth (e.wedge p.1)
  coefficient := fun p => insertedCoefficient (fun a => if a=i then 1 else 0)
    (e.coefficient p.1) (e.wedge p.1) p.2
  formula := by
    have h (j : Fin 5) : b.coord i (KaehlerDifferential.D k R (x j)) = if j=i then 1 else 0 := by
      rw [← hb j]; exact b.repr_self_apply j i
    rw [e.formula]
    exact interior_expansion_with (b.coord i) x _ h e.terms n e.wedge e.coefficient
  homogeneous := fun p hp => sparse_term (e.wedge p.1) i p.2
    (e.homogeneous p.1 (Finset.mem_product.mp hp).1)

end WeightedExpansion
variable {v M x}

private theorem weight_five : exteriorWeight (id : Fin 5 → Fin 5) = 6 := by
  norm_num [exteriorWeight,geometricWeight,Fin.sum_univ_succ]

/-- An arbitrary represented scalar times the native coordinate volume. -/
def scalarVolume (b : Frame k R) (hb : ∀ i, b i = KaehlerDifferential.D k R (x i))
    {c : R} {d : ℤ} (hc : Represented v M d c) :
    WeightedExpansion v M x (d+6) 5 (c • volume b) where
  index := Unit
  terms := {()}
  wedge := fun _ => id
  coefficient := fun _ => c
  formula := by
    simp only [Finset.sum_singleton]
    exact congrArg (fun m : Fin 5 → Ω[R⁄k] => c • exteriorPower.ιMulti R 5 m) (funext hb)
  homogeneous := by
    intro a _
    simpa [weight_five] using hc

/-- The uncontracted vertex numerator has total weight six. -/
def top_expansion (b : Frame k R) (hb : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (c : R) (hc : Represented v M 0 c) : WeightedExpansion v M x 6 5 (top b c) :=
  scalarVolume b hb hc

/-- The signed four-form attached to the edge coefficients. -/
def flux_expansion (b : Frame k R) (hb : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (c : Fin 5 → R) (hc : ∀ i, Represented v M (geometricWeight i : ℤ) (c i)) :
    WeightedExpansion v M x 6 4 (flux b c) := by
  change WeightedExpansion _ _ _ 6 4 (∑ i, c i • interior 4 (b.coord i) (volume b))
  apply WeightedExpansion.sum
  intro i
  rw [← map_smul]
  exact (show (geometricWeight i : ℤ) + 6 - geometricWeight i = 6 by omega) ▸
    (scalarVolume b hb (hc i)).contract b hb i

/-- The ordered coordinate contractions in the upper-triangular three-form
also preserve total weight six. -/
def biv_expansion (b : Frame k R) (hb : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (c : Fin 5 → Fin 5 → R)
    (hc : ∀ i j, Represented v M ((geometricWeight i : ℤ) + geometricWeight j) (c i j)) :
    WeightedExpansion v M x 6 3 (biv b c) := by
  change WeightedExpansion _ _ _ 6 3 (∑ i, ∑ j, c i j •
    (if i<j then interior 3 (b.coord i) (interior 4 (b.coord j) (volume b)) else 0))
  apply WeightedExpansion.sum
  intro i
  apply WeightedExpansion.sum
  intro j
  by_cases h : i<j
  · rw [if_pos h,← map_smul,← map_smul]
    exact (show (geometricWeight i : ℤ) + geometricWeight j + 6 - geometricWeight j -
      geometricWeight i = 6 by omega) ▸
        ((scalarVolume b hb (hc i j)).contract b hb j).contract b hb i
  · rw [if_neg h,smul_zero]
    exact WeightedExpansion.zero

end CycleQ2WeightedCofactorExpansions
end

#print axioms CycleQ2WeightedCofactorExpansions.top_expansion
#print axioms CycleQ2WeightedCofactorExpansions.flux_expansion
#print axioms CycleQ2WeightedCofactorExpansions.biv_expansion
