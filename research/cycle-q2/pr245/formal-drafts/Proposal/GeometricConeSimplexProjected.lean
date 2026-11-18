import Proposal.GeometricConeSimplexBoundary
import Proposal.GeometricConeSimplexRadialClosure

/-! Weighted Euler projection gives a total degree-three cocycle on the gradient nerve. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexCochain

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2ConeSimplexRings (Divisor)
open CycleQ2LogarithmicPullback (Forms)
open CycleQ2ConeSimplexRadialClosure (radialize radialize_restrict)
open CycleQ2LogarithmicDifferential (exteriorD)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k)
local notation "G" => equation φ

/-- On every cone simplex the weighted radial vector gives the horizontal
form that can be restricted to a local section of the weighted quotient. -/
def project {p : ℕ} (n : ℕ) (z : (x : Fin (p+1) → Fin 5) → Forms k (Divisor G (support x)) (n+1))
    (x : Fin (p+1) → Fin 5) : Forms k (Divisor G (support x)) n :=
  radialize φ (support x) n (z x)

abbrev projectedVertex := project φ 3 (vertex φ)
abbrev projectedEdge := project φ 2 (edge φ)
abbrev projectedFace := project φ 1 (face φ)

theorem delta_project {p : ℕ} (n : ℕ)
    (z : (x : Fin (p+1) → Fin 5) → Forms k (Divisor G (support x)) (n+1)) (x : Fin (p+2) → Fin 5) :
    delta φ n (project φ n z) x = radialize φ (support x) n (delta φ (n+1) z x) := by
  simp only [delta, project, map_sum, map_zsmul, radialize_restrict]

theorem projected_vertex_closed (x : Fin 1 → Fin 5) :
    exteriorD (tupleBasis φ x) 3 (projectedVertex φ x) = 0 := by
  by_cases h : Regular φ (support x)
  · change exteriorD _ 3 (radialize φ (support x) 3 (rV φ (support x) _ _)) = 0
    rw [rV_eq φ h]
    exact (CycleQ2ConeSimplexRadialClosure.vertex_on φ (support x) h (x 0) (mem_support x 0)
      (x 0) (mem_support x 0)).2
  · exact (empty_forms φ h 4).elim _ _

theorem projected_edge_derivative (x : Fin 2 → Fin 5) :
    exteriorD (tupleBasis φ x) 2 (projectedEdge φ x) = delta φ 3 (projectedVertex φ) x := by
  by_cases h : Regular φ (support x)
  · let T := support x
    let hi := mem_support x 0
    let hj := mem_support x 1
    have hc := (CycleQ2ConeSimplexRadialClosure.edge_on φ T h (x 0) hi (x 0) (x 1) hi hj).2
    change exteriorD _ 2 (radialize φ T 2 (rE φ T hi hi hj)) = _
    rw [rE_eq φ h, hc, delta_project]
    rw [← neg_eq_iff_eq_neg.mpr (edge_derivative φ x)]
    change _ = radialize φ T 3 (-exteriorD _ 3 (rE φ T hi hi hj))
    rw [d_rE, map_neg, map_sub, neg_sub, rV_eq φ h, rV_eq φ h] <;> rfl
  · exact (empty_forms φ h 3).elim _ _

theorem projected_face_derivative (x : Fin 3 → Fin 5) :
    exteriorD (tupleBasis φ x) 1 (projectedFace φ x) = -delta φ 2 (projectedEdge φ) x := by
  by_cases h : Regular φ (support x)
  · let T := support x
    let hi := mem_support x 0
    let hj := mem_support x 1
    let hl := mem_support x 2
    have hc := (CycleQ2ConeSimplexRadialClosure.face_on φ T h (x 0) hi (x 0) (x 1) (x 2)
      hi hj hl).2
    change exteriorD _ 1 (radialize φ T 1 (rF φ T hi hi hj hl)) = _
    rw [rF_eq φ h, hc, delta_project, ← face_derivative]
    change _ = -radialize φ T 2 (exteriorD _ 2 (rF φ T hi hi hj hl))
    rw [d_rF, map_add, map_sub, rE_eq φ h, rE_eq φ h, rE_eq φ h] <;> rfl
  · exact (empty_forms φ h 2).elim _ _

theorem projected_faces_close (x : Fin 4 → Fin 5) :
    delta φ 1 (projectedFace φ) x = 0 := by rw [delta_project, faces_close, map_zero]

end CycleQ2ConeSimplexCochain
end

#print axioms CycleQ2ConeSimplexCochain.projected_vertex_closed
#print axioms CycleQ2ConeSimplexCochain.projected_edge_derivative
#print axioms CycleQ2ConeSimplexCochain.projected_face_derivative
#print axioms CycleQ2ConeSimplexCochain.projected_faces_close
