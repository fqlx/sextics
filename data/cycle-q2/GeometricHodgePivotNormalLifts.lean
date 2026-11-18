import Proposal.GeometricHodgeTwistGradientUnits
import Proposal.GeometricHodgeEulerSheaf
import Proposal.GeometricHodgeFermatYukawaDeterminant

/-!
# Normal lifts on the moving four-open projective atlas

On D₊(xᵢFᵢ) the normalized i-th partial is invertible. In any common
coordinate frame the single surviving component of a normal lift is
the degree-six numerator divided by that partial. This calculation
takes place over the original coefficient ring and commutes with restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgePivotNormalLifts

open AlgebraicGeometry CategoryTheory Limits
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2HodgeEulerSheaf
open CycleQ2HodgeTwistGradientCover (pivotOpen pivotOpen_le normalized_partial_isUnit)
open CycleQ2HodgeAtlasLine (coordinate_restrict restrictRing)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)
open CycleQ2SeedSectionSheafLimits (sectionProductEquiv sectionProductEquiv_apply sectionProductEquiv_symm_apply)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)
variable (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ pivotOpen φ i)

abbrev sourceChart := hi.trans (pivotOpen_le φ i)

theorem partial_isUnit (a : Fin 4) (ha : V ≤ U φ a) :
    IsUnit (normalized φ a (partialValue φ i.castSucc) (partial_mem φ i.castSucc) V ha) := by
  rw [normalized_change φ a i _ _ V ha (sourceChart φ i V hi)]
  exact (((transition φ a i V ha (sourceChart φ i V hi)).isUnit).pow _).mul
    (normalized_partial_isUnit φ i V hi)

def inverse (a : Fin 4) (ha : V ≤ U φ a) : Γ(threefold φ,V) := ↑(partial_isUnit φ i V hi a ha).unit⁻¹

theorem inverse_partial (a : Fin 4) (ha : V ≤ U φ a) :
    inverse φ i V hi a ha * normalized φ a (partialValue φ i.castSucc) (partial_mem φ i.castSucc) V ha = 1 :=
  (partial_isUnit φ i V hi a ha).val_inv_mul

theorem inverse_restrict (a : Fin 4) (ha : V ≤ U φ a) {W : (threefold φ).Opens} (h : W ≤ V) :
    restrictRing (X := threefold φ) h (inverse φ i V hi a ha) =
      inverse φ i W (h.trans hi) a (h.trans ha) := by
  let q := normalized φ a (partialValue φ i.castSucc) (partial_mem φ i.castSucc) W (h.trans ha)
  let r := restrictRing (X := threefold φ) h
  have hr : r (inverse φ i V hi a ha) * q = 1 := by
    have he := congrArg r (inverse_partial φ i V hi a ha)
    rw [map_mul, map_one] at he
    exact (congrArg (r (inverse φ i V hi a ha) * ·)
      (normalized_restrict φ a (partialValue φ i.castSucc) (partial_mem φ i.castSucc) ha h).symm).trans he
  have hw : inverse φ i W (h.trans hi) a (h.trans ha) * q = 1 :=
    inverse_partial φ i W (h.trans hi) a (h.trans ha)
  change r (inverse φ i V hi a ha) = _
  calc
    _ = r (inverse φ i V hi a ha) * (inverse φ i W (h.trans hi) a (h.trans ha) * q) := by rw [hw, mul_one]
    _ = (r (inverse φ i V hi a ha) * q) * inverse φ i W (h.trans hi) a (h.trans ha) := by ring
    _ = _ := by rw [hr, one_mul]

variable (p : grade φ 6)

def lift : Γ(raw φ,V) :=
  (sectionProductEquiv (pieces φ) V).symm fun a =>
    (chartFrame φ (geometricWeight a) i V (sourceChart φ i V hi)).symm
      (if a = i.castSucc then inverse φ i V hi i (sourceChart φ i V hi) *
        normalized φ i p.val p.property V (sourceChart φ i V hi) else 0)

theorem lift_frame (a : Fin 5) :
    chartFrame φ (geometricWeight a) i V (sourceChart φ i V hi) ((Pi.π (pieces φ) a).app V (lift φ i V hi p)) =
      if a = i.castSucc then inverse φ i V hi i (sourceChart φ i V hi) *
        normalized φ i p.val p.property V (sourceChart φ i V hi) else 0 := by
  simp only [lift, sectionProductEquiv_symm_apply, LinearEquiv.apply_symm_apply]

theorem lift_normal : (normalMap φ).app V (lift φ i V hi p) = homogeneousSection φ p.val p.property V := by
  apply (chartFrame φ 6 i V (sourceChart φ i V hi)).injective
  rw [normal_frame, homogeneousSection_coordinate]
  simp_rw [lift_frame]
  rw [Finset.sum_eq_single i.castSucc]
  · rw [if_pos rfl, ← mul_assoc, mul_comm _ (inverse φ i V hi i _), inverse_partial, one_mul]
  · intro a _ ha
    rw [if_neg ha, mul_zero]
  · simp

theorem lift_restrict {W : (threefold φ).Opens} (h : W ≤ V) :
    moduleRes (raw φ) h (lift φ i V hi p) = lift φ i W (h.trans hi) p := by
  apply (sectionProductEquiv (pieces φ) W).injective
  funext a
  rw [sectionProductEquiv_apply, sectionProductEquiv_apply, ← moduleRes_app]
  apply (chartFrame φ (geometricWeight a) i W (sourceChart φ i W (h.trans hi))).injective
  refine (coordinate_restrict (cocycle φ (geometricWeight a)) i (sourceChart φ i V hi) h _).trans ?_
  change restrictRing (X := threefold φ) h
    (chartFrame φ _ i V _ ((Pi.π (pieces φ) a).app V (lift φ i V hi p))) = _
  rw [lift_frame, lift_frame]
  by_cases ha : a = i.castSucc
  · rw [if_pos ha, if_pos ha, map_mul, inverse_restrict, normalized_restrict]
  · rw [if_neg ha, if_neg ha, map_zero]

abbrev read (a : Fin 4) (ha : V ≤ U φ a) (j : Fin 5) :=
  chartFrame φ (geometricWeight j) a V ha ((Pi.π (pieces φ) j).app V (lift φ i V hi p))

theorem read_zero (a : Fin 4) (ha : V ≤ U φ a) (j : Fin 5) (hj : j ≠ i.castSucc) :
    read φ i V hi p a ha j = 0 := by
  change chartFrame φ _ a V ha _ = 0
  rw [chartFrame_transition φ _ a i V ha (sourceChart φ i V hi), lift_frame, if_neg hj, mul_zero]

theorem read_pivot (a : Fin 4) (ha : V ≤ U φ a) :
    read φ i V hi p a ha i.castSucc = normalized φ a p.val p.property V ha * inverse φ i V hi a ha := by
  have hn := congrArg (chartFrame φ 6 a V ha) (lift_normal φ i V hi p)
  rw [normal_frame, homogeneousSection_coordinate] at hn
  change (∑ j, normalized φ a (partialValue φ j) (partial_mem φ j) V ha * read φ i V hi p a ha j) = _ at hn
  rw [Finset.sum_eq_single i.castSucc (fun j _ hj => by rw [read_zero φ i V hi p a ha j hj, mul_zero]) (by simp)] at hn
  rw [← hn]
  calc
    _ = (inverse φ i V hi a ha * normalized φ a (partialValue φ i.castSucc) (partial_mem φ i.castSucc) V ha) *
          read φ i V hi p a ha i.castSucc := by rw [inverse_partial, one_mul]
    _ = _ := by ring

theorem read_lift (h : ∀ j : Fin 4, V ≤ pivotOpen φ j) :
    read φ i V hi p 0 (sourceChart φ 0 V (h 0)) =
      CycleQ2HodgeFermatYukawaDeterminant.lift (fun j => inverse φ j V (h j) 0 (sourceChart φ 0 V (h 0)))
        i (normalized φ 0 p.val p.property V (sourceChart φ 0 V (h 0))) := by
  funext j
  by_cases hj : j = i.castSucc
  · subst j
    simp only [CycleQ2HodgeFermatYukawaDeterminant.lift, if_pos rfl, read_pivot]
  · simp only [CycleQ2HodgeFermatYukawaDeterminant.lift, if_neg hj, read_zero φ i V hi p 0 _ j hj]

end CycleQ2HodgePivotNormalLifts
end
#print axioms CycleQ2HodgePivotNormalLifts.lift_normal
#print axioms CycleQ2HodgePivotNormalLifts.read_lift
