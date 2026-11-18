import Proposal.GeometricHodgeCyclicCharts
import Proposal.GeometricHodgeEulerTangentCoordinates
import Proposal.GeometricHiggsJacobianMembership

/-!
# Pullback of normalized homogeneous sections on the moving threefold

A degree-n numerator pulls back on the i-th frame with the inverse n-th
power of the character of its denominator. Correcting this frame factor
recovers the original action on all homogeneous sections and gives the
degree-six character of the normal direction of the deformation.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicTwistFrames

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
  CycleQ2GenericSexticGradient CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding CycleQ2GeometricHodgeThreefold
  CycleQ2HodgeCyclicAction CycleQ2GeometricIncidenceProj CycleQ2LiteralThreefoldOrbitAction
  CycleQ2HodgeEulerTangentCoordinates CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
  CycleQ2HodgeTwistRatios CycleQ2ChartSectionPullback
  CycleQ2SeedCyclicAction CycleQ2LiteralOrbitAction

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (i : Fin 4)
abbrev g := (action φ z hz).hom
abbrev scalar (V : (threefold φ).Opens) := coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) V

variable (V W : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) (hi' : W ≤ coordinateOpen φ i)
  (hWV : W ≤ g φ z hz ⁻¹ᵁ V)

theorem affine_pull (a : chart φ i) :
    (g φ z hz).appLE V W hWV (chartSection (affineChart φ i) (Over.mk (homOfLE hi)) a) =
      chartSection (affineChart φ i) (Over.mk (homOfLE hi')) (CycleQ2HodgeCyclicAction.chartAction φ z hz i a) :=
  chartSection_pullback (g φ z hz) (affineChart φ i) (affineChart φ i)
    (CycleQ2HodgeCyclicAction.chartAction φ z hz i).toRingHom (coordinateOpen_stable φ z hz i).ge
    (by simpa only [affineInclusion, Category.assoc] using affineInclusion_equivariant φ z hz i)
    V hi W hi' hWV a

theorem normalized_pull {n : ℕ} (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (g φ z hz).appLE V W hWV (normalized φ i (quotient φ p) (quotient_mem_grade φ _ hp) V hi) =
      scalar φ W (baseScale z i^n) * normalized φ i (quotient φ (polynomialAction z p))
        (quotient_mem_grade φ _ (polynomialAction_weighted z hp)) W hi' := by
  rw [← chartSection_normalized, affine_pull φ z hz i V W hi hi' hWV, ← chartSection_normalized]
  change chartSection (affineChart φ i) (Over.mk (homOfLE hi')) (chartMap φ i (chartPoly z i (dehom i p))) = _
  rw [chartPoly_dehom z hz i p hp, map_mul, map_mul]
  exact congrArg (fun c => c * _) (chartSection_complex (affineChart φ i) (toBase φ)
    (affineChart_overBase φ i) (Over.mk (homOfLE hi')) (baseScale z i^n))

theorem character_pull {n : ℕ} (χ : ZMod 3) (p : MvPolynomial (Fin 5) ℂ)
    (hp : CycleQ2IncidenceEquations.HG p (n,χ)) :
    (g φ z hz).appLE V W hWV
        (normalized φ i (quotient φ p) (quotient_mem_grade φ _ (homogeneous_of_character hp)) V hi) =
      scalar φ W (baseScale z i^n * z^χ.val) *
        normalized φ i (quotient φ p) (quotient_mem_grade φ _ (homogeneous_of_character hp)) W hi' := by
  let q := chartSection (affineChart φ i) (Over.mk (homOfLE hi'))
  have cq (a : ℂ) : q (chartMap φ i (C a)) = scalar φ W a :=
    chartSection_complex (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
      (Over.mk (homOfLE hi')) a
  rw [← chartSection_normalized, affine_pull φ z hz i V W hi hi' hWV, ← chartSection_normalized]
  change q (chartMap φ i (chartPoly z i (dehom i p))) = _
  rw [chartPoly_dehom z hz i p (homogeneous_of_character hp), polynomialAction_homogeneous z hz p n χ hp]
  simp only [map_mul, show dehom i (C (z^χ.val)) = C _ from aeval_C _ _, cq, mul_assoc]

theorem coordinate_pull (a : Fin 5) :
    (g φ z hz).appLE V W hWV (normalized φ i (coord φ a) (coord_mem_grade φ a) V hi) =
      scalar φ W (factor z i a) * normalized φ i (coord φ a) (coord_mem_grade φ a) W hi' := by
  let q := chartSection (affineChart φ i) (Over.mk (homOfLE hi'))
  rw [← chartSection_coordinate, affine_pull φ z hz i V W hi hi' hWV, ← chartSection_coordinate]
  change q (chartMap φ i (chartPoly z i (dehom i (X a)))) = _ * q (chartMap φ i (dehom i (X a)))
  have hw := isWeightedHomogeneous_X ℂ geometricWeight a
  have cq (c : ℂ) : q (chartMap φ i (C c)) = scalar φ W c :=
    chartSection_complex (affineChart φ i) (toBase φ) (affineChart_overBase φ i) (Over.mk (homOfLE hi')) c
  rw [chartPoly_dehom z hz i _ hw, action_X]
  simp only [map_mul, show dehom i (C (char z a)) = C _ from aeval_C _ _, cq, factor]
  ring

theorem ratio_pull (j : Fin 4) :
    (g φ z hz).appLE V W hWV (CycleQ2HodgeTwistRatios.ratio φ i j V hi) =
      scalar φ W (char z j.castSucc * baseScale z i) * CycleQ2HodgeTwistRatios.ratio φ i j W hi' := by
  simpa only [factor, CycleQ2SeedFermatProj.geometricWeight_castSucc, pow_one] using
    coordinate_pull φ z hz i V W hi hi' hWV j.castSucc

include hz in
private theorem gradient_factor (a : Fin 5) :
    baseScale z i ^ (6 - geometricWeight a) * z ^ (-(CycleQ2IncidenceNormalForm.fullGrading a).2).val =
      (factor z i a)⁻¹ := by
  have hchar : z ^ (-(CycleQ2IncidenceNormalForm.fullGrading a).2).val * char z a = 1 := by
    fin_cases a
    all_goals first | exact one_mul 1 | change z * z^2 = 1; linear_combination hz |
      change z^2 * z = 1; linear_combination hz | change z^0 * 1 = 1; simp
  have hw : geometricWeight a ≤ 6 := by fin_cases a <;> decide
  have hbase : baseScale z i ^ (6 - geometricWeight a) * baseScale z i ^ geometricWeight a = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hw, baseScale_six z hz]
  apply eq_inv_of_mul_eq_one_left
  unfold factor
  calc
    _ = (baseScale z i ^ (6 - geometricWeight a) * baseScale z i ^ geometricWeight a) *
        (z ^ (-(CycleQ2IncidenceNormalForm.fullGrading a).2).val * char z a) := by ring
    _ = 1 := by rw [hbase, hchar, mul_one]

theorem gradient_pull (a : Fin 5) :
    (g φ z hz).appLE V W hWV (normalized φ i (CycleQ2HodgeEulerSheaf.partialValue φ a)
      (CycleQ2HodgeEulerSheaf.partial_mem φ a) V hi) =
      scalar φ W (factor z i a)⁻¹ * normalized φ i (CycleQ2HodgeEulerSheaf.partialValue φ a)
        (CycleQ2HodgeEulerSheaf.partial_mem φ a) W hi' := by
  have hgrad := CycleQ2HiggsJacobianMembership.partial_homogeneous φ a
  have hw : (CycleQ2IncidenceNormalForm.fullGrading a).1 = geometricWeight a := by fin_cases a <;> rfl
  rw [hw] at hgrad
  simpa only [gradient_factor z hz i a] using character_pull φ z hz i V W hi hi' hWV _ _ hgrad

end CycleQ2HodgeCyclicTwistFrames
end

#print axioms CycleQ2HodgeCyclicTwistFrames.ratio_pull

#print axioms CycleQ2HodgeCyclicTwistFrames.gradient_pull
