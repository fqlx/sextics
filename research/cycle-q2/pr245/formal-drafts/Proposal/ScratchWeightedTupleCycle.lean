import Proposal.ScratchWeightedSectionCochains
import Proposal.ScratchWeightedNativeCech

/-! Assembly of a class from the actual sections of the even and odd
Čech columns. The edge and face equations are evaluated on the actual
double, triple and quadruple intersections with their native restriction maps. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2.Cech CycleQ2CechDeRhamTotalThree CycleQ2WeightedResidueAtlas
  CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient CycleQ2WeightedNativeCech
  CycleQ2WeightedSectionCochains CycleQ2LogarithmicDifferential
namespace CycleQ2WeightedTupleCycle
variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)
local notation "U'" => U φ
local notation "P'" => Native.P (toBase φ)
local notation "B'" => double φ
abbrev FormOn (p q : ℕ) (x : Fin (p+1) → Index) := (P' q).obj (op (intersection U' x))
abbrev Family (p q : ℕ) := ∀ x : Fin (p+1) → Index, FormOn φ p q x

def restrictFace {p q : ℕ} (z : Family φ p q) (x : Fin (p+2) → Index)
    (j : Fin (p+2)) : FormOn φ (p+1) q x :=
  (P' q).map (faceRestriction U' x j).op (z (x ∘ j.succAbove))

abbrev d {p q : ℕ} (z : Family φ p q) (x : Fin (p+1) → Index) :=
  exteriorD ((frames φ).basis p x) q (z x)

/-- Three families of ordinary sections with the alternating Čech/exterior
derivative equations give a class in the total kernel on this threefold. -/
def cycle (v : Family φ 0 3) (e : Family φ 1 2) (f : Family φ 2 1)
    (hv : ∀ x, d φ v x = 0)
    (he : ∀ x, d φ e x = restrictFace φ v x 0 - restrictFace φ v x 1)
    (hf : ∀ x, d φ f x = -(restrictFace φ e x 0-restrictFace φ e x 1+restrictFace φ e x 2))
    (ht : ∀ x, restrictFace φ f x 0-restrictFace φ f x 1+
      restrictFace φ f x 2-restrictFace φ f x 3 = 0) : Cycles B' := by
  apply simplexResidueCycle U' P' (Native.simplex (toBase φ) U' (frames φ))
    v (fun x => -e x) f hv
  · intro x
    rw [tupleDelta_zero]
    change restrictFace φ v x 0 - restrictFace φ v x 1 = -(_ (-e x))
    rw [map_neg,neg_neg]
    exact (he x).symm
  · intro x
    rw [tupleDelta_one,hf]
    simp only [tupleFace,restrictFace,map_neg] <;> abel
  · intro x
    rw [tupleDelta_two]
    exact ht x

end CycleQ2WeightedTupleCycle
end
#print axioms CycleQ2WeightedTupleCycle.cycle
