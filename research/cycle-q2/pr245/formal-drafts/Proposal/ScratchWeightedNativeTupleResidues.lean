import Proposal.ScratchWeightedSectionFaces
import Proposal.ScratchWeightedTupleCycle
import Proposal.GeometricConeSimplexExpansion
import Proposal.GeometricConeSimplexProjected

/-! The signed projected residue on each simplex of the actual proper threefold.
The equations are transported from the localization of the cone, using the
actual structure-sheaf face restrictions and the relative exterior derivative. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace CycleQ2WeightedNativeTupleResidues
open CycleQ2.Cech
open CycleQ2WeightedSectionCochains (read simplexMonoid)
open CycleQ2WeightedTupleCycle (restrictFace Family)
open CycleQ2WeightedResidueAtlas (Index U normalIndex)
open CycleQ2WeightedRepresentedForms (Expansion projected)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation toBase)
open CycleQ2HodgeEulerContractionRestriction (pull)
open CycleQ2LogarithmicPullback (Forms)
open CycleQ2WeightedSectionFaces (read_d face_pull)
open CycleQ2ConeSimplexCochain (support vertexExpansion edgeExpansion faceExpansion mem_support
  projectedVertex projectedEdge projectedFace projected_vertex_closed projected_edge_derivative
  projected_face_derivative projected_faces_close)
variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k)

abbrev vertex : Family φ 0 3 := fun v => pull (read φ v 0) 3 (projectedVertex φ (normalIndex ∘ v))
abbrev edge : Family φ 1 2 := fun v => pull (read φ v 0) 2 (projectedEdge φ (normalIndex ∘ v))
abbrev face : Family φ 2 1 := fun v => pull (read φ v 0) 1 (projectedFace φ (normalIndex ∘ v))

private theorem delta_projected {p : ℕ} (n : ℕ)
    (ω : (x : Fin (p+1) → Fin 5) → Forms k (CycleQ2ConeSimplexRings.Divisor (equation φ) (support x)) (n+2))
    (E : ∀ v : Fin (p+1) → Index, Expansion φ (simplexMonoid φ v) (n+2) (ω (normalIndex ∘ v)))
    (v : Fin (p+2) → Index) :
    tupleDelta (U φ) (Native.P (toBase φ)) p (n+1)
      (fun w => pull (read φ w 0) (n+1) (CycleQ2ConeSimplexCochain.project φ (n+1) ω (normalIndex ∘ w))) v =
    pull (read φ v 0) (n+1) (CycleQ2ConeSimplexCochain.delta φ (n+1)
      (CycleQ2ConeSimplexCochain.project φ (n+1) ω) (normalIndex ∘ v)) := by
  simp only [tupleDelta,CycleQ2ConeSimplexCochain.delta,map_sum,map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z => (-1:ℤ)^j.val • z)
  let w := CycleQ2WeightedSectionFaces.face v j
  change pull _ (n+1) (pull (read φ w 0) (n+1) (-(projected φ _ n (ω (normalIndex ∘ w))))) =
    pull (read φ v 0) (n+1) (pull (CycleQ2WeightedSectionFaces.coneFace φ v j) (n+1)
      (-(projected φ _ n (ω (normalIndex ∘ w)))))
  simp only [map_neg]
  exact congrArg Neg.neg (face_pull φ v j n (ω (normalIndex ∘ w)) (E w))

theorem vertex_closed (v : Fin 1 → Index) :
    CycleQ2WeightedTupleCycle.d φ (vertex φ) v = 0 := by
  change CycleQ2LogarithmicDifferential.exteriorD _ 3 (pull (read φ v 0) 3 _) = 0
  rw [read_d,projected_vertex_closed,map_zero]

theorem edge_d (v : Fin 2 → Index) :
    CycleQ2WeightedTupleCycle.d φ (edge φ) v = restrictFace φ (vertex φ) v 0 - restrictFace φ (vertex φ) v 1 := by
  change CycleQ2LogarithmicDifferential.exteriorD _ 2 (pull (read φ v 0) 2 _) = _
  rw [read_d,projected_edge_derivative]
  have h := delta_projected φ 2 (CycleQ2ConeSimplexCochain.vertex φ)
    (fun w => vertexExpansion φ _ (mem_support _ 0) (mem_support _ 0)) v
  rw [← h]
  exact tupleDelta_zero _ _ _ _ v

theorem face_d (v : Fin 3 → Index) :
    CycleQ2WeightedTupleCycle.d φ (face φ) v =
      -(restrictFace φ (edge φ) v 0 - restrictFace φ (edge φ) v 1 + restrictFace φ (edge φ) v 2) := by
  change CycleQ2LogarithmicDifferential.exteriorD _ 1 (pull (read φ v 0) 1 _) = _
  rw [read_d, projected_face_derivative, map_neg]
  have h := delta_projected φ 1 (CycleQ2ConeSimplexCochain.edge φ)
    (fun w => edgeExpansion φ _ (mem_support _ 0) (mem_support _ 0) (mem_support _ 1)) v
  rw [← h]
  exact congrArg Neg.neg (tupleDelta_one _ _ _ _ v)

theorem quadruple_closed (v : Fin 4 → Index) :
    restrictFace φ (face φ) v 0 - restrictFace φ (face φ) v 1 +
      restrictFace φ (face φ) v 2 - restrictFace φ (face φ) v 3 = 0 := by
  have h := delta_projected φ 0 (CycleQ2ConeSimplexCochain.face φ)
    (fun w => faceExpansion φ _ (mem_support _ 0) (mem_support _ 0) (mem_support _ 1) (mem_support _ 2)) v
  rw [projected_faces_close,map_zero] at h
  exact (tupleDelta_two _ _ _ _ v).symm.trans h

end CycleQ2WeightedNativeTupleResidues
end
#print axioms CycleQ2WeightedNativeTupleResidues.vertex_closed
#print axioms CycleQ2WeightedNativeTupleResidues.edge_d
#print axioms CycleQ2WeightedNativeTupleResidues.face_d
#print axioms CycleQ2WeightedNativeTupleResidues.quadruple_closed
