import Proposal.GeometricIncidenceCechTrace
import Proposal.GeometricProjectiveFrames

/-!
# Positive twists on the original incidence curve

Two quartic denominator opens cover the curve. A homogeneous overlap section
of weight at least two splits into sections on these opens. The reduction
uses the degree-nine bound for the quotient by the two quartics and the
original quadratic and cubic equations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCurvePositiveTwist

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricIncidenceCechSurjectivity

private abbrev overlapCoord (i : Fin 4) : Overlap 57 1 :=
  algebraMap (CurveRing 57 1) (Overlap 57 1) (curveMap 57 1 (X i))

private def Splits (k : ℕ) (z : Overlap 57 1) : Prop :=
  ∃ (a : FirstProjectiveRing 57 1) (b : SecondProjectiveRing 57 1),
    (firstProjectiveRestriction 57 1 a).val * overlapCoord 1 ^ k +
      (secondProjectiveRestriction 57 1 b).val * overlapCoord 2 ^ k = z

private theorem splits_add {k : ℕ} {u v : Overlap 57 1}
    (hu : Splits k u) (hv : Splits k v) : Splits k (u + v) := by
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, d, rfl⟩ := hv
  refine ⟨a + c, b + d, ?_⟩
  simp only [map_add, HomogeneousLocalization.val_add, add_mul]
  abel

private theorem patch_frame (f x g : CurveRing 57 1) (hf : f ∈ curveGrade 57 1 4)
    (hg : g ∈ curveGrade 57 1 3) (hfg : f = x * g) (k n : ℕ)
    (p : Poly) (hp : p.IsHomogeneous (k + 4 * n)) :
    ∃ a : HomogeneousLocalization.Away (curveGrade 57 1) f,
      a.val * algebraMap (CurveRing 57 1) (Localization.Away f) x ^ k =
        awayFraction 57 1 f n (curveMap 57 1 p) := by
  have hgrade : curveMap 57 1 p * g ^ k ∈ curveGrade 57 1 ((n + k) • 4) := by
    have hpow : g ^ k ∈ curveGrade 57 1 (k • 3) := SetLike.pow_mem_graded k hg
    have hd : k + 4 * n + k • 3 = (n + k) • 4 := by
      simp only [nsmul_eq_mul, Nat.cast_id]
      omega
    rw [← hd]
    exact SetLike.mul_mem_graded (curveMap_mem_grade 57 1 hp) hpow
  refine ⟨HomogeneousLocalization.Away.mk (curveGrade 57 1) hf (n + k) _ hgrade, ?_⟩
  rw [HomogeneousLocalization.Away.val_mk, ← map_pow, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, awayFraction, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Subtype.coe_mk, one_mul, mul_one]
  rw [pow_add, hfg, mul_pow]
  ring

private theorem splits_first (k n : ℕ) (p : Poly) (hp : p.IsHomogeneous (k + 4 * n)) :
    Splits k (mixedFraction n 0 (curveMap 57 1 p)) := by
  obtain ⟨a, h⟩ := patch_frame _ _ _ (curveG1_mem_grade 57 1) (firstFrameComplement_grade 57 1)
    (firstFrame_factorization 57 1) k n p hp
  refine ⟨a, 0, ?_⟩
  simp only [map_zero, HomogeneousLocalization.val_zero, zero_mul, add_zero]
  have hres := congrArg (awayRestriction 57 1 (curveG1 57 1) (curveG2 57 1)
    (curveG1 57 1 * curveG2 57 1) rfl) h
  simpa only [firstProjectiveRestriction, awayRestriction_val, map_mul, map_pow,
    awayRestriction_base, awayRestriction_fraction, mixedFraction, Nat.add_zero, pow_zero,
    mul_one] using hres

private theorem splits_second (k m : ℕ) (p : Poly) (hp : p.IsHomogeneous (k + 4 * m)) :
    Splits k (mixedFraction 0 m (curveMap 57 1 p)) := by
  obtain ⟨b, h⟩ := patch_frame _ _ _ (curveG2_mem_grade 57 1) (secondFrameComplement_grade 57 1)
    (secondFrame_factorization 57 1) k m p hp
  refine ⟨0, b, ?_⟩
  simp only [map_zero, HomogeneousLocalization.val_zero, zero_mul, zero_add]
  have hres := congrArg (awayRestriction 57 1 (curveG2 57 1) (curveG1 57 1)
    (curveG1 57 1 * curveG2 57 1) (mul_comm _ _)) h
  simpa only [secondProjectiveRestriction, awayRestriction_val, map_mul, map_pow,
    awayRestriction_base, awayRestriction_fraction, mixedFraction, Nat.zero_add, pow_zero,
    mul_one] using hres

private theorem mixedFraction_splits (k : ℕ) (hk : 2 ≤ k) (n m : ℕ)
    (p : Poly) (hp : p.IsHomogeneous (k + 4 * (n + m))) :
    Splits k (mixedFraction n m (curveMap 57 1 p)) := by
  suffices aux : ∀ s n m : ℕ, n + m = s → ∀ p : Poly,
      p.IsHomogeneous (k + 4 * (n + m)) → Splits k (mixedFraction n m (curveMap 57 1 p)) by
    exact aux (n + m) n m rfl p hp
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro n m hs p hp
    cases n with
    | zero => exact splits_second k m p (by simpa using hp)
    | succ n =>
      cases m with
      | zero => exact splits_first k (n + 1) p (by simpa using hp)
      | succ m =>
        have hhigh : 9 < k + 4 * ((n + 1) + (m + 1)) := by omega
        obtain ⟨c, d, hc, hd, heq⟩ := high_degree_curve_relation hhigh p hp
        rw [heq, mixedFraction_add, mixedFraction_mul_first, mixedFraction_mul_second]
        apply splits_add
        · apply ih (n + (m + 1)) (by omega) n (m + 1) rfl c
          convert hc using 1
          omega
        · apply ih ((n + 1) + m) (by omega) (n + 1) m rfl d
          convert hd using 1
          omega

/-- With the transition of the actual two coordinate frames, every overlap
section of weight at least two is a difference of regular chart sections. -/
theorem positiveTwist_difference_surjective (k : ℕ) (hk : 2 ≤ k) (z : OverlapProjectiveRing 57 1) :
    ∃ (a : FirstProjectiveRing 57 1) (b : SecondProjectiveRing 57 1),
      firstProjectiveRestriction 57 1 a - overlapTransition 57 1 ^ k *
        secondProjectiveRestriction 57 1 b = z := by
  obtain ⟨n, u, hu, hzu⟩ := HomogeneousLocalization.Away.mk_surjective
    (curveGrade 57 1) (curveG12_mem_grade 57 1) z
  obtain ⟨p, hp, hpu⟩ : ∃ p : Poly, p.IsHomogeneous (n • 8) ∧ curveMap 57 1 p = u := hu
  have hpk : (p * (X 1) ^ k).IsHomogeneous (k + 4 * (n + n)) := by
    convert hp.mul ((isHomogeneous_X (R := ℂ) (1 : Fin 4)).pow k) using 1 <;>
      simp only [nsmul_eq_mul, Nat.cast_id] <;> omega
  obtain ⟨a,b,hab⟩ := mixedFraction_splits k hk n n _ hpk
  refine ⟨a, -b, ?_⟩
  apply HomogeneousLocalization.val_injective
  apply ((frameCoordinate_isUnit 57 1 _ _ _ (overlapFirstFrame_factorization 57 1)).pow k).mul_right_cancel
  rw [map_neg, HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_neg, HomogeneousLocalization.val_pow, mul_neg, sub_neg_eq_add, add_mul]
  have hsecond : (overlapTransition 57 1).val ^ k * (secondProjectiveRestriction 57 1 b).val *
      overlapCoord 1 ^ k = (secondProjectiveRestriction 57 1 b).val * overlapCoord 2 ^ k := by
    rw [mul_right_comm, ← mul_pow, overlapTransition_coordinate]
    exact mul_comm _ _
  rw [hsecond, hab, mixedFraction_balanced, map_mul, map_pow, hpu, ← hzu,
    HomogeneousLocalization.Away.val_mk]
  change awayFraction 57 1 _ n (u * curveMap 57 1 (X 1) ^ k) =
    awayFraction 57 1 _ n u * algebraMap (CurveRing 57 1) (Overlap 57 1) (curveMap 57 1 (X 1)) ^ k
  rw [← (algebraMap (CurveRing 57 1) (Overlap 57 1)).map_pow,
    ← Localization.mk_one_eq_algebraMap, awayFraction, awayFraction, Localization.mk_mul, mul_one]

end CycleQ2LiteralCurvePositiveTwist
end

#print axioms CycleQ2LiteralCurvePositiveTwist.positiveTwist_difference_surjective
