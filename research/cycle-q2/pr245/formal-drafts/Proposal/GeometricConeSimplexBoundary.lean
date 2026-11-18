import Proposal.GeometricConeSimplexCochain
import Proposal.GeometricConeSimplexClosure

/-! Unsigned residues of the cubic-pole cochains on the entire gradient Čech nerve. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexCochain

open MvPolynomial CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2ConeSimplexRings (restrictDivisor Divisor)
open CycleQ2LogarithmicChartDerivative (pull)
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2LogarithmicPullback (Forms)
open CycleQ2ConeSimplexClosure (vertex_on edge_on face_on tetrahedron_on)
open CycleQ2ConeSimplexNumerator (v_restrict e_restrict f_restrict)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k) {T U : Finset (Fin 5)}
local notation "G" => equation φ

/-- Restricting from any face allows the first index used as the normal to change. -/
theorem pull_rV (h : T ⊆ U) {r s i : Fin 5} (hr : r ∈ T) (hs : s ∈ U) (hi : i ∈ T) :
    pull (restrictDivisor G h) 4 (rV φ T hr hi) = rV φ U hs (h hi) := by
  by_cases hU : Regular φ U
  · have hT : Regular φ T := fun i hi => hU i (h hi)
    rw [rV_eq φ hT, rV_eq φ hU, pull_res φ h hr hs 3 _
      (vertex_on φ T hT r hr i hi).1, v_restrict φ h hU]
  · exact (empty_forms φ hU 4).elim _ _

theorem pull_rE (h : T ⊆ U) {r s i j : Fin 5} (hr : r ∈ T) (hs : s ∈ U)
    (hi : i ∈ T) (hj : j ∈ T) :
    pull (restrictDivisor G h) 3 (rE φ T hr hi hj) = rE φ U hs (h hi) (h hj) := by
  by_cases hU : Regular φ U
  · have hT : Regular φ T := fun i hi => hU i (h hi)
    rw [rE_eq φ hT, rE_eq φ hU, pull_res φ h hr hs 2 _
      (edge_on φ T hT r hr i j hi hj).1, e_restrict φ h hU]
  · exact (empty_forms φ hU 3).elim _ _

theorem pull_rF (h : T ⊆ U) {r s i j l : Fin 5} (hr : r ∈ T) (hs : s ∈ U)
    (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    pull (restrictDivisor G h) 2 (rF φ T hr hi hj hl) = rF φ U hs (h hi) (h hj) (h hl) := by
  by_cases hU : Regular φ U
  · have hT : Regular φ T := fun i hi => hU i (h hi)
    rw [rF_eq φ hT, rF_eq φ hU, pull_res φ h hr hs 1 _
      (face_on φ T hT r hr i j l hi hj hl).1, f_restrict φ h hU]
  · exact (empty_forms φ hU 2).elim _ _

local notation "F" => CycleQ2GradientSimplex.divisorBasis G (T : Set (Fin 5))

theorem d_rV {r i : Fin 5} (hr : r ∈ T) (hi : i ∈ T) :
    exteriorD (F r hr) 4 (rV φ T hr hi) = 0 := by
  by_cases hT : Regular φ T
  · rw [rV_eq φ hT]
    exact (vertex_on φ T hT r hr i hi).2
  · exact (empty_forms φ hT 5).elim _ _

theorem d_rE {r i j : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T) :
    exteriorD (F r hr) 3 (rE φ T hr hi hj) = rV φ T hr hi - rV φ T hr hj := by
  by_cases hT : Regular φ T
  · simp only [rV_eq φ hT, rE_eq φ hT]
    exact (edge_on φ T hT r hr i j hi hj).2
  · exact (empty_forms φ hT 4).elim _ _

theorem d_rF {r i j l : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    exteriorD (F r hr) 2 (rF φ T hr hi hj hl) =
      rE φ T hr hj hl - rE φ T hr hi hl + rE φ T hr hi hj := by
  by_cases hT : Regular φ T
  · simp only [rF_eq φ hT, rE_eq φ hT]
    exact (face_on φ T hT r hr i j l hi hj hl).2
  · exact (empty_forms φ hT 3).elim _ _

theorem tetra {r i j l m : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T)
    (hl : l ∈ T) (hm : m ∈ T) :
    rF φ T hr hj hl hm - rF φ T hr hi hl hm + rF φ T hr hi hj hm - rF φ T hr hi hj hl = 0 := by
  by_cases hT : Regular φ T
  · simp only [rF_eq φ hT]
    exact tetrahedron_on φ T hT r hr i j l m hi hj hl hm
  · exact (empty_forms φ hT 2).elim _ _

/-- Deleting one index restricts a section to precisely the common derivative
localization of all the entries, including repetitions. -/
abbrev omit {n : ℕ} (x : Fin (n+1) → Fin 5) (j : Fin (n+1)) := x ∘ j.succAbove

def delta {p : ℕ} (q : ℕ)
    (z : (x : Fin (p+1) → Fin 5) → Forms k (Divisor G (support x)) q)
    (x : Fin (p+2) → Fin 5) : Forms k (Divisor G (support x)) q :=
  ∑ j : Fin (p+2), (-1 : ℤ)^j.val •
    pull (restrictDivisor G (support_mono x j.succAbove)) q (z (omit x j))

private theorem face_vertex (x : Fin 2 → Fin 5) (a : Fin 2) :
    pull (restrictDivisor G (support_mono x a.succAbove)) 4 (vertex φ (omit x a)) =
      rV φ (support x) (mem_support x 0) (mem_support x (a.succAbove 0)) :=
  pull_rV φ (support_mono x a.succAbove) _ _ _

private theorem face_edge (x : Fin 3 → Fin 5) (a : Fin 3) :
    pull (restrictDivisor G (support_mono x a.succAbove)) 3 (edge φ (omit x a)) =
      rE φ (support x) (mem_support x 0) (mem_support x (a.succAbove 0))
        (mem_support x (a.succAbove 1)) :=
  pull_rE φ (support_mono x a.succAbove) _ _ _ _

private theorem face_face (x : Fin 4 → Fin 5) (a : Fin 4) :
    pull (restrictDivisor G (support_mono x a.succAbove)) 2 (face φ (omit x a)) =
      rF φ (support x) (mem_support x 0) (mem_support x (a.succAbove 0))
        (mem_support x (a.succAbove 1)) (mem_support x (a.succAbove 2)) :=
  pull_rF φ (support_mono x a.succAbove) _ _ _ _ _

theorem vertex_closed (x : Fin 1 → Fin 5) : exteriorD (tupleBasis φ x) 4 (vertex φ x) = 0 :=
  d_rV φ _ _

theorem edge_derivative (x : Fin 2 → Fin 5) :
    exteriorD (tupleBasis φ x) 3 (edge φ x) = -delta φ 4 (vertex φ) x := by
  rw [edge, d_rE]
  simp only [delta, face_vertex, Fin.sum_univ_two]
  change _ = -((1 : ℤ) • rV φ _ (mem_support x 0) (mem_support x 1) +
    (-1 : ℤ) • rV φ _ (mem_support x 0) (mem_support x 0))
  simp only [one_smul, neg_one_smul, neg_add_rev, neg_neg, sub_eq_add_neg]

theorem face_derivative (x : Fin 3 → Fin 5) :
    exteriorD (tupleBasis φ x) 2 (face φ x) = delta φ 3 (edge φ) x := by
  rw [face, d_rF]
  simp only [delta, face_edge, Fin.sum_univ_three]
  change _ = (1 : ℤ) • rE φ _ (mem_support x 0) (mem_support x 1) (mem_support x 2) +
    (-1 : ℤ) • rE φ _ (mem_support x 0) (mem_support x 0) (mem_support x 2) +
    (1 : ℤ) • rE φ _ (mem_support x 0) (mem_support x 0) (mem_support x 1)
  simp only [one_smul, neg_one_smul, sub_eq_add_neg]

theorem faces_close (x : Fin 4 → Fin 5) : delta φ 2 (face φ) x = 0 := by
  simp only [delta, face_face, Fin.sum_univ_four]
  change (1 : ℤ) • rF φ _ (mem_support x 0) (mem_support x 1) (mem_support x 2) (mem_support x 3) +
    (-1 : ℤ) • rF φ _ (mem_support x 0) (mem_support x 0) (mem_support x 2) (mem_support x 3) +
    (1 : ℤ) • rF φ _ (mem_support x 0) (mem_support x 0) (mem_support x 1) (mem_support x 3) +
    (-1 : ℤ) • rF φ _ (mem_support x 0) (mem_support x 0) (mem_support x 1) (mem_support x 2) = 0
  simp only [one_smul, neg_one_smul, ← sub_eq_add_neg]
  exact tetra φ _ _ _ _ _

end CycleQ2ConeSimplexCochain
end

#print axioms CycleQ2ConeSimplexCochain.vertex_closed
#print axioms CycleQ2ConeSimplexCochain.edge_derivative
#print axioms CycleQ2ConeSimplexCochain.face_derivative
#print axioms CycleQ2ConeSimplexCochain.faces_close
