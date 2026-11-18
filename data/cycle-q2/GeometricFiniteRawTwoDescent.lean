import Proposal.GeometricCechRefinement

/-!
# Finite Čech descent from adjacent-repeat vanishing

For a closed degree-two cochain the reverse-edge values account for its
nonzero faces of the form `(i,j,i)`. Subtracting their coboundary makes the
cochain alternating while preserving every weakly increasing face.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FiniteRawTwoDescent

open CategoryTheory Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent

variable {X : TopCat.{0}} {ι : Type} {F : AbSheaf X} (U : ι → Opens X)
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _

private def edgeBoundary (g : One F U) : Two F U := fun i j k =>
  boundaryValue F U g i j k _ (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right

private theorem face_boundary (g : One F U) (i j k : ι) W hi hj hk :
    faceValue F U (edgeBoundary U g) i j k W hi hj hk = boundaryValue F U g i j k W hi hj hk := by
  simp only [edgeBoundary, faceValue, boundaryValue, edgeValue, map_add, map_sub, res_comp]

variable [LinearOrder ι]

/-- Only descending edges need a correction. -/
def reverseEdge (c : Two F U) : One F U := fun i j =>
  if j < i then faceValue F U c i j i _ inf_le_left inf_le_right inf_le_left else 0

private theorem reverseEdge_value (c : Two F U) (i j : ι) W hi hj :
    edgeValue F U (reverseEdge U c) i j W hi hj =
      if j < i then faceValue F U c i j i W hi hj hi else 0 := by
  by_cases h : j < i <;> simp only [edgeValue, reverseEdge, faceValue, h, if_true, if_false,
    res_comp, map_zero]

/-- Normalize by the actual coboundary over the pair intersections. -/
def normalize (c : Two F U) : Two F U := c - edgeBoundary U (reverseEdge U c)

private theorem normalize_value (c : Two F U) (i j k : ι) W hi hj hk :
    faceValue F U (normalize U c) i j k W hi hj hk =
    faceValue F U c i j k W hi hj hk - boundaryValue F U (reverseEdge U c) i j k W hi hj hk := by
  rw [normalize, faceValue_sub, face_boundary]

theorem normalize_face_of_le (c : Two F U) {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceValue F U (normalize U c) i j k W hi hj hk = faceValue F U c i j k W hi hj hk := by
  simp only [normalize_value, boundaryValue, reverseEdge_value, if_neg (not_lt_of_ge hij),
    if_neg (not_lt_of_ge hjk), if_neg (not_lt_of_ge (hij.trans hjk)), sub_zero, zero_add]

theorem normalize_apply_of_le (c : Two F U) {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    normalize U c i j k = c i j k := by
  simpa only [faceValue, res_self] using normalize_face_of_le U c hij hjk
    ((U i ⊓ U j) ⊓ U k) (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right

theorem normalize_closed (c : Two F U) (hc : IsTwoCocycle F U c) :
    IsTwoCocycle F U (normalize U c) := by
  intro i j k l W hi hj hk hl
  simp only [normalize_value, boundaryValue]
  linear_combination (norm := abel) hc i j k l W hi hj hk hl

theorem normalize_normalized (c : Two F U)
    (h12 : ∀ i k W hi hk, faceValue F U c i i k W hi hi hk = 0)
    (h23 : ∀ i j W hi hj, faceValue F U c i j j W hi hj hj = 0)
    (hc : IsTwoCocycle F U c) : NormalizedTwo F U (normalize U c) := by
  have r12 (i k : ι) W hi hk : faceValue F U (normalize U c) i i k W hi hi hk = 0 := by
    rw [normalize_value, h12]
    simp only [boundaryValue, sub_self, zero_add, reverseEdge_value, lt_irrefl, if_false, sub_zero]
  have r23 (i j : ι) W hi hj : faceValue F U (normalize U c) i j j W hi hj hj = 0 := by
    rw [normalize_value, h23]
    simp only [boundaryValue, reverseEdge_value, lt_irrefl, if_false, zero_sub, neg_add_cancel,
      sub_zero]
  have r13 (i j : ι) W hi hj : faceValue F U (normalize U c) i j i W hi hj hi = 0 := by
    have h := hc i j i j W hi hj hi hj
    rw [h12, h23, sub_zero, add_zero, sub_eq_zero] at h
    rcases lt_trichotomy i j with hl | heq | hl
    · simp only [normalize_value, boundaryValue, reverseEdge_value, if_pos hl, lt_irrefl,
        if_false, if_neg (not_lt_of_gt hl), sub_zero, add_zero, h, sub_self]
    · subst j
      exact r12 i i W hi hi
    · simp only [normalize_value, boundaryValue, reverseEdge_value, if_pos hl, lt_irrefl,
        if_false, if_neg (not_lt_of_gt hl), sub_zero, zero_add, sub_self]
  have hn := normalize_closed U c hc
  refine ⟨r12, r23, ?_, ?_⟩
  · intro i j k W hi hj hk
    have h := hn j i j k W hj hi hj hk
    rw [r12, r13] at h
    linear_combination (norm := abel) h
  · intro i j k W hi hj hk
    have h := hn i j k j W hi hj hk hj
    rw [r13, r23] at h
    linear_combination (norm := abel) -h

/-- Undoing the normalization gives a descent of the original cochain. -/
theorem exists_raw_descent [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (h12 : ∀ i k W hi hk, faceValue F U c i i k W hi hi hk = 0)
    (h23 : ∀ i j W hi hj, faceValue F U c i j j W hi hj hj = 0)
    (hc : IsTwoCocycle F U c) : Nonempty (TwoDescent U c) := by
  obtain ⟨d⟩ := twoDescent_nonempty U hcover (normalize U c)
    (normalize_normalized U c h12 h23 hc) (normalize_closed U c hc)
  let q := edgeBoundary U (reverseEdge U c)
  have hq : ∀ i j k W hi hj hk, boundaryValue F U (-(reverseEdge U c)) i j k W hi hj hk =
      faceValue F U (-q) i j k W hi hj hk := by
    intro i j k W hi hj hk
    change _ = res F _ (-(q i j k))
    rw [map_neg]
    change _ = -faceValue F U (edgeBoundary U (reverseEdge U c)) i j k W hi hj hk
    rw [face_boundary]
    simp only [boundaryValue, edgeValue, Pi.neg_apply, map_neg]
    abel
  let d' := subtractDescents U d (boundaryDescent U (-(reverseEdge U c)) hq)
  have he : normalize U c - (-q) = c := by
    change c - q - (-q) = c
    abel
  exact ⟨he ▸ d'⟩

/-- Normalizing a raw representative preserves its actual derived class. -/
theorem descentClass_normalize [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (d : TwoDescent U c) (e : TwoDescent U (normalize U c)) :
    descentClass U e = descentClass U d := by
  have h := descentClass_eq_zero_of_boundary U hcover (subtractDescents U d e) (reverseEdge U c)
    (by
      intro i j k W hi hj hk
      rw [faceValue_sub, normalize_value]
      abel)
  rw [descentClass_sub] at h
  exact (sub_eq_zero.mp h).symm

end CycleQ2FiniteRawTwoDescent

end

#print axioms CycleQ2FiniteRawTwoDescent.normalize_face_of_le
#print axioms CycleQ2FiniteRawTwoDescent.normalize_normalized
#print axioms CycleQ2FiniteRawTwoDescent.exists_raw_descent

#print axioms CycleQ2FiniteRawTwoDescent.descentClass_normalize
