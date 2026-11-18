import Proposal.GeometricProjectorUnitDefect

/-!
# Base change of the marked projector transition

Writing a common matrix in a coordinate frame introduces a unit factor in
every entry. It cancels between the pivot and the entry giving the transition
of the raw columns.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2ProjectorMappedPivot

open CategoryTheory AlgebraicGeometry Matrix CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralMovingDivisorChern CycleQ2GeometricRankOneImage
  CycleQ2ProjectorUnitDefect

variable {V : Surface.Opens} {E L : Type*} [CommRing E] [CommRing L]

/-- The common homogeneous unit cancels from the ratio over any base ring. -/
theorem mapped_pivot_ratio (f g : FrameData V) (φ : Γ(Surface,V) →+* L)
    (M : Matrix (Fin 3) (Fin 3) L) (s u : Lˣ)
    (hM : M = (s : L) • (sectionMatrix f.chart V f.within).map φ)
    (hu : (u : L) = M f.pivot.1 f.pivot.2) :
    (↑(u⁻¹) : L) * M f.pivot.1 g.pivot.2 = φ (columnTransition f g : Γ(Surface,V)) := by
  have entry (i j : Fin 3) : M i j = (s : L) * φ (sectionMatrix f.chart V f.within i j) :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) L => A i j) hM
  have hp : (f.pivotUnit : Γ(Surface,V)) * (columnTransition f g : Γ(Surface,V)) =
      sectionMatrix f.chart V f.within f.pivot.1 g.pivot.2 := by
    rw [columnTransition_val, mul_comm _ (↑(f.pivotUnit⁻¹) : Γ(Surface,V)),
      Units.mul_inv_cancel_left]
  have hcancel : (u : L) * φ (columnTransition f g : Γ(Surface,V)) = M f.pivot.1 g.pivot.2 := by
    calc
      _ = ((s : L) * φ (↑f.pivotUnit)) * φ (columnTransition f g : Γ(Surface,V)) := by
          rw [hu, entry, f.pivot_eq]
      _ = (s : L) * φ ((↑f.pivotUnit : Γ(Surface,V)) * ↑(columnTransition f g)) := by
          rw [map_mul, mul_assoc]
      _ = M f.pivot.1 g.pivot.2 := (congrArg (fun z => (s : L) * φ z) hp).trans (entry _ _).symm
  rw [← hcancel, Units.inv_mul_cancel_left]

/-- For the raw matrix columns the reduced transition unit is exactly the
base-changed moving-divisor transition with its pivot coboundary. -/
theorem transition_reduction_mapped_movingSystem (t : Fin 3 → ℂ)
    (ht : ∀ i, ChartRegular t i) (f g : FrameData V) (φ : Γ(Surface,V) →+* L)
    (M : Matrix (Fin 3) (Fin 3) L) (s u : Lˣ)
    (hM : M = (s : L) • (sectionMatrix f.chart V f.within).map φ)
    (hu : (u : L) = M f.pivot.1 f.pivot.2)
    (ρ : E →+* L) (w : Fin 3 × Fin 3 → L) (hw : ∑ q, w q * M q.1 q.2 = 1)
    {e e' : Matrix (Fin 3) (Fin 3) E} (a : Frame e) (b : Frame e')
    (hy : ρ ∘ a.y = (↑(u⁻¹) : L) • (projectorMatrix M w).row f.pivot.1)
    (hx : ρ ∘ b.x = M.col g.pivot.2)
    (v : Eˣ) (hv : (v : E) = transition a b) :
    Units.map ρ.toMonoidHom v = Units.map φ.toMonoidHom
      ((movingSystem t ht).value f g * g.pivotUnit * f.pivotUnit⁻¹) := by
  have entry (i j : Fin 3) : M i j = (s : L) * φ (sectionMatrix f.chart V f.within i j) :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) L => A i j) hM
  have minors (i j k l : Fin 3) : M i j * M k l = M k j * M i l := by
    have h := congrArg φ ((CycleQ2SegreLocal.minors_of_cofactors_zero _
      (sectionMatrix_cofactors f) i j k l).trans (mul_comm _ _))
    simp only [map_mul] at h
    simp only [entry]
    linear_combination (s : L)^2 * h
  apply Units.ext
  change ρ (v : E) = φ _
  rw [hv, transition_reduction_of_pivots ρ M minors w hw f.pivot g.pivot.2 u a b hy hx,
    mapped_pivot_ratio f g φ M s u hM hu, columnTransition_eq_movingSystem t ht]

end CycleQ2ProjectorMappedPivot

end

#print axioms CycleQ2ProjectorMappedPivot.mapped_pivot_ratio
#print axioms CycleQ2ProjectorMappedPivot.transition_reduction_mapped_movingSystem
