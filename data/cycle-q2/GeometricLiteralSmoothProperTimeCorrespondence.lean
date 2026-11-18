import Proposal.GeometricLiteralTimeFamilyRefinement
import Proposal.GeometricLiteralTimeCorrespondenceStrictTransform
import Proposal.GeometricLiteralAbelJacobiTimeTrace
import Proposal.GeometricLiteralProperSweptSupport
import Proposal.GeometricLiteralTimeMarkedIntegralBranch
import Proposal.GeometricLiteralTimeNormalizationSmooth
import Proposal.GeometricLiteralTimeCurveBoundary

/-!
# The complete smooth branch carrying the fixed-sextic correspondence

Choose the actual independent parameters with nonzero embedded normal
and restrict the moving family to the marked affine integral branch.
Its normalized completion is a smooth proper integral complex curve.
The closure of the family in its product with the fixed threefold is a
proper correspondence, dense along the original family, with both
original projections and the nonconstant marked time direction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralSmoothProperTimeCorrespondence
open CategoryTheory AlgebraicGeometry CycleQ2LiteralIncidenceTimeCurve
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceFirstOrder
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralTimeCurveNormalization CycleQ2LiteralTimeCorrespondenceStrictTransform
  CycleQ2IncidenceSeedFiberCover CycleQ2FirstOrderChartReduction
  CycleQ2LiteralAbelJacobiRelativeNormal CycleQ2LiteralMovingCurveDifferentialNonzero
  CycleQ2LiteralMovingCurveKodairaSpencer CycleQ2LiteralSheafOneClasses
  CycleQ2SeedSectionAffineInjective
open TopologicalSpace CategoryTheory.Limits

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

private abbrev toOldClosure (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :=
  embedding V t ≫ CycleQ2LiteralTimeNormalizedCorrespondence.toOriginalClosure V t

private theorem toOldClosure_fixed (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :
    toOldClosure V t ≫ CycleQ2LiteralTimeCorrespondenceCompletion.fixedProjection V t =
      fixedProjection V t := by
  simp only [toOldClosure, fixedProjection, CycleQ2LiteralTimeNormalizedCorrespondence.toFixed,
    Category.assoc]

theorem swept_ideal (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :
    (fixedProjection V t).ker = (q V t).ker := by
  apply le_antisymm
  · rw [← inclusion_toFixed V t]
    exact (inclusion V t).le_ker_comp _
  · rw [← CycleQ2LiteralProperSweptSupport.fixedProjection_ker V t, ← toOldClosure_fixed]
    exact (toOldClosure V t).le_ker_comp _

theorem swept_range (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :
    Set.range (fixedProjection V t) = Set.range (q V t).imageι := by
  change Set.range (fixedProjection V t) = Set.range (q V t).ker.subschemeι
  rw [Scheme.IdealSheafData.range_subschemeι, ← swept_ideal, Scheme.Hom.support_ker,
    (fixedProjection V t).isClosedMap.isClosed_range.closure_eq]

/-- The moving family with nonzero normal is the dense open family of a
closed proper correspondence on a smooth proper integral pointed curve. -/
theorem exists_correspondence :
    ∃ (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V),
      AlgebraicIndependent ℚ t ∧
      AlgebraicGeometry.IsIntegral (Normalization (timeOpen V)) ∧
      SmoothOfRelativeDimension 1 (toComplexPoint (timeOpen V)) ∧
      IsProper (toComplexPoint (timeOpen V)) ∧
      ((Set.range (openInclusion (timeOpen V)))ᶜ).Finite ∧
      SmoothOfRelativeDimension 1 (projection V t) ∧ IsProper (projection V t) ∧
      Function.Surjective (projection V t) ∧
      SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex) ∧
      IsClosedImmersion (intoProduct V t) ∧ IsOpenImmersion (inclusion V t) ∧ IsDominant (inclusion V t) ∧
      IsProper (baseProjection V t) ∧ Function.Surjective (baseProjection V t) ∧
      IsProper (fixedProjection V t) ∧
      (fixedProjection V t).ker = (q V t).ker ∧
      Set.range (fixedProjection V t) = closure (Set.range (q V t)) ∧
      Set.range (fixedProjection V t) ≠ Set.univ ∧
      IsPullback (projection V t) (inclusion V t) (openInclusion (timeOpen V)) (baseProjection V t) ∧
      inclusion V t ≫ fixedProjection V t = q V t ∧
      tangentLift V hV ≫ openInclusion (timeOpen V) ≠
        structureDual ≫ seedLift V hV ≫ openInclusion (timeOpen V) ∧
      (firstOrderIso V t hV).hom ≫ pullback.snd _ _ ≫ inclusion V t ≫ fixedProjection V t =
        (CycleQ2LiteralIncidenceTimeFamily.firstOrderIso t).hom ≫ pullback.snd _ _ ≫
          CycleQ2LiteralIncidenceCylinderMap.toFixedThreefold t ∧
      restrictContraction t kodairaSpencerDerivedClass = curveClass t ∧
      differentialTrace t ht (curveClass t) ≠ 0 ∧
      ∃ hf : ∀ i, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
        ∃ j : Fin 3, @relativeNormal t j.succ (hf j.succ)
          ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 := by
  obtain ⟨t, hi, ht, V, hV, _, hd, _, hp, hs, _, hn⟩ := exists_smooth_time_family
  let U := CycleQ2LiteralTimeMarkedIntegralBranch.branch V hV
  obtain ⟨W, hWV, hWU⟩ := CycleQ2LiteralTimeFamilyRefinement.exists_parameter_refinement V U
    (CycleQ2LiteralTimeMarkedIntegralBranch.branch_le V hV)
  have hW : seedBasePoint ∈ W := by
    have hm : seed default ∈ timeOpen W := by
      rw [hWU]
      exact CycleQ2LiteralTimeMarkedIntegralBranch.marked_mem V hV
    change (seed ≫ toIncidence) (default : Spec (CommRingCat.of ℂ)) ∈ W at hm
    rw [seed_to_incidence] at hm
    simpa only [seedBasePoint, CycleQ2IncidenceChartFiberScheme.seedParameterMorphism,
      seedPointMorphism, parameterScheme] using hm
  let : IsAffine (timeOpen W).toScheme := by
    rw [hWU]
    exact CycleQ2LiteralTimeMarkedIntegralBranch.branch_affine V hV
  let : AlgebraicGeometry.IsIntegral (timeOpen W).toScheme := by
    rw [hWU]
    exact CycleQ2LiteralTimeMarkedIntegralBranch.branch_integral V hV
  let : AlgebraicGeometry.IsIntegral (Normalization (timeOpen W)) :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral
      (CycleQ2LiteralTimeCurveCompletion.inclusion (timeOpen W)).normalization)
  obtain ⟨hd',hp',hs'⟩ := CycleQ2LiteralTimeFamilyRefinement.restrict_properties hWV t hd hp hs
  let := smooth_parameter_curve
  let : SmoothOfRelativeDimension 1 ((timeOpen W).ι ≫ toComplex) := smoothOfRelativeDimension_comp 0 1 _ _
  let : SmoothOfRelativeDimension 1 (projection W t) := hd'
  obtain ⟨hr, hproperImage, _⟩ := CycleQ2LiteralSweptSupport.swept_image W t hW
    (smoothOfRelativeDimension_comp 1 1 _ _) hp' hs'
  refine ⟨t,ht,W,hW, hi, inferInstance, CycleQ2LiteralTimeNormalizationSmooth.smooth_curve _,
    inferInstance, (CycleQ2LiteralTimeCurveBoundary.normalization_boundary _).1,
    hd', hp', hs', smoothOfRelativeDimension_comp 1 1 _ _, inferInstance, inferInstance,
    inferInstance, inferInstance,
    covers_normalized_base W t hs',
    inferInstance, swept_ideal W t, (swept_range W t).trans hr, (swept_range W t).trans_ne hproperImage,
    recovery W t, inclusion_toFixed W t, ?_, ?_, restrictContraction_kodairaSpencer t,
    differentialTrace_curveClass_ne_zero t ht, hn⟩
  · intro he
    apply tangentLift_nonconstant W hW
    apply (cancel_mono (openInclusion (timeOpen W))).mp
    simpa only [Category.assoc] using he
  · rw [inclusion_toFixed]
    exact firstOrder_to_q W t hW

end CycleQ2LiteralSmoothProperTimeCorrespondence
end

#print axioms CycleQ2LiteralSmoothProperTimeCorrespondence.exists_correspondence
