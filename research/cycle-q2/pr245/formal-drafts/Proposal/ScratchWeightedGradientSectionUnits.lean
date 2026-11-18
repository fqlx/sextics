import Proposal.ScratchWeightedOwnGradientUnit
import Proposal.ScratchWeightedResidueAtlas
import Proposal.ScratchWeightedNativeOverlapSection
import Proposal.ScratchWeightedCechPresentations
import Proposal.ScratchCechComplexFaces

/-! The homogeneous partial derivatives selecting the vertices of a Čech simplex
are units in its actual ring of regular functions, in every weight-one
normalization available on that open. Thus the entire denominator monoid
of the cone differential maps to units.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2WeightedGradientSectionUnits

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2.Cech CycleQ2.Cech.Sections CycleQ2GenericSexticGradient
  CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerTangentCoordinates
  CycleQ2HodgeEulerSheaf CycleQ2HodgeEulerChartBinding CycleQ2GeometricAffineChartSections
  CycleQ2WeightedResidueAtlas CycleQ2WeightedNativeOverlapSection
  CycleQ2WeightedOwnGradientUnit CycleQ2WeightedCechPresentations
open CycleQ2HodgeTwistRatios (normalized_change transition)

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)

theorem patch_le_coordinate (a : Index) : U φ a ≤ coordinateOpen φ a.1 :=
  ((inclusion φ a.1).image_le_opensRange _).trans (inclusion_range φ a.1).le

/-- Evaluating a cone polynomial at its normalized structure sections agrees
with its dehomogenization in the project's affine chart. -/
theorem eval_coordAt (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (p : MvPolynomial (Fin 5) k) :
    letI := algebra (toBase φ) W
    aeval (coordAt φ i W hi) p = chartAlg φ i W hi (chartMap φ i (dehom i p)) := by
  letI := algebra (toBase φ) W
  have e : aeval (coordAt φ i W hi) =
      (chartAlg φ i W hi).comp ((chartMap φ i).comp (dehom i)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [aeval_X, AlgHom.comp_apply]
    exact (chartAlg_coordinate φ i W hi j).symm
  exact AlgHom.congr_fun e p

/-- The actual normalized section lies on the sextic. -/
theorem eval_equation_zero (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) :
    letI := algebra (toBase φ) W
    aeval (coordAt φ i W hi) (equation φ) = 0 := by
  letI := algebra (toBase φ) W
  rw [eval_coordAt]
  change chartAlg φ i W hi (chartMap φ i (F φ i)) = 0
  rw [chartMap_F, map_zero]

/-- A derivative chosen at any one vertex remains invertible when evaluated
using any other weight-one pivot admitted by the common open. -/
theorem derivative_section_unit (a : Index) (i : Fin 4) (W : (threefold φ).Opens)
    (hW : W ≤ U φ a) (hi : W ≤ coordinateOpen φ i) :
    letI := algebra (toBase φ) W
    IsUnit (aeval (coordAt φ i W hi) (pderiv (normalIndex a) (equation φ))) := by
  letI := algebra (toBase φ) W
  rw [eval_coordAt]
  change IsUnit (chartSection (affineChart φ i) (Over.mk (homOfLE hi))
    (conePartial φ i (normalIndex a)))
  rw [chartSection_partial]
  let ha := hW.trans (patch_le_coordinate φ a)
  rw [normalized_change φ i a.1 _ (partial_mem φ (normalIndex a)) W hi ha]
  exact ((transition φ i a.1 W hi ha).isUnit.pow _).mul (own_gradient_unit φ a W hW ha)

theorem unit_on_commonOpen {I : Type*} (v : I → Index) (i : Fin 4)
    (W : (threefold φ).Opens) (hW : ∀ a, W ≤ U φ (v a)) (hi : W ≤ coordinateOpen φ i) :
    letI := algebra (toBase φ) W
    ∀ m : denominators (equation φ) (Set.range (normalIndex ∘ v)),
      IsUnit (aeval (coordAt φ i W hi) (m : MvPolynomial (Fin 5) k)) := by
  letI := algebra (toBase φ) W
  intro m
  refine denominators_map_units (equation φ) _ (aeval (coordAt φ i W hi)).toRingHom ?_ m
  rintro _ ⟨a, rfl⟩
  exact derivative_section_unit φ (v a) i W (hW a) hi

theorem unit_on_simplex {p : ℕ} (v : Fin (p+1) → Index) (j : Fin (p+1)) :
    let W := intersection (U φ) v
    let hi := (intersection_le (U φ) v j).trans (patch_le_coordinate φ (v j))
    letI := algebra (toBase φ) W
    ∀ m : denominators (equation φ) (Set.range (normalIndex ∘ v)),
      IsUnit (aeval (coordAt φ (v j).1 W hi) (m : MvPolynomial (Fin 5) k)) :=
  unit_on_commonOpen φ v (v j).1 _ (intersection_le (U φ) v) _

end CycleQ2WeightedGradientSectionUnits
end
#print axioms CycleQ2WeightedGradientSectionUnits.unit_on_simplex
