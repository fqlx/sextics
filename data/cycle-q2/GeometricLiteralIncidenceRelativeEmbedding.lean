import Proposal.GeometricLiteralIncidenceRelativeCylinder
import Proposal.GeometricLiteralTimeFamilyEmbedding

/-!
# The relative incidence family as a closed correspondence

Together, the time point and its point on the ambient sextic determine the
embedded section point. Properness over the time curve then identifies the
relative family with a closed subscheme of the product over the coefficient base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceRelativeEmbedding

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFamilyContainment CycleQ2RelativeConstantCurve
  CycleQ2LiteralIncidenceCylinderMap CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceRelativeCylinder

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

variable {B : Scheme} (i : B ⟶ sexticBase) (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev Product := pullback (timeMap i V) (pullback.fst i universalAmbientToBase)

def joint : Surface i V t ⟶ Product i V :=
  pullback.lift (curveMap i V t) (relativeQ i V t) (relativeQ_fst i V t).symm

@[reassoc (attr := simp)] theorem joint_toTime :
    joint i V t ≫ pullback.fst _ _ = curveMap i V t := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem joint_toAmbient :
    joint i V t ≫ pullback.snd _ _ = relativeQ i V t := pullback.lift_snd _ _ _

private theorem curve_to_parameter :
    curveMap i V t ≫ pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι =
      toOriginal i V t ≫ relativeCurveToBase incidencePoint t := by
  let f := relativeCurveToBase incidencePoint t
  change pullback.fst _ (f ∣_ V) ≫ pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι =
    (pullback.snd _ (f ∣_ V) ≫ (f ⁻¹ᵁ V).ι) ≫ f
  rw [← Category.assoc, pullback.condition, Category.assoc, morphismRestrict_ι, Category.assoc]

private abbrev inclusion := relativeCurveToSurface incidencePoint t ≫ surfaceToThreefold incidencePoint

private theorem original_ext {W : Scheme} (g h : W ⟶ relativeCurve incidencePoint t)
    (hbase : g ≫ relativeCurveToBase incidencePoint t = h ≫ relativeCurveToBase incidencePoint t)
    (hambient : g ≫ originalToAmbient t = h ≫ originalToAmbient t) : g = h := by
  have : IsClosedImmersion (surfaceToThreefold incidencePoint) := by
    apply CycleQ2LiteralAmbientSurface.projectiveMap_closedImmersion
    rintro n b ⟨p, hp, rfl⟩
    exact ⟨Ideal.Quotient.mk (sexticIdeal incidencePoint) p, ⟨p, hp, rfl⟩, rfl⟩
  apply (cancel_mono (inclusion t)).mp
  apply CycleQ2LiteralTimeFamilyEmbedding.coefficient_joint_ext
    sexticToParameter universalPoint incidencePoint universal_to_incidence
  · simpa only [inclusion, Category.assoc, surfaceToThreefold_toBase, relativeCurveToBase] using hbase
  · simpa only [inclusion, Category.assoc, originalToAmbient] using hambient

theorem joint_mono : Mono (joint i V t) := by
  constructor
  intro W g h he
  have ht : g ≫ curveMap i V t = h ≫ curveMap i V t := by
    simpa only [Category.assoc, joint_toTime] using congrArg (· ≫ pullback.fst _ _) he
  have hq : g ≫ relativeQ i V t = h ≫ relativeQ i V t := by
    simpa only [Category.assoc, joint_toAmbient] using congrArg (· ≫ pullback.snd _ _) he
  have ho : g ≫ toOriginal i V t = h ≫ toOriginal i V t := by
    apply original_ext
    · simpa only [Category.assoc, curve_to_parameter] using
        congrArg (· ≫ pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι) ht
    · simpa only [Category.assoc, relativeQ_snd] using
        congrArg (· ≫ pullback.snd i universalAmbientToBase) hq
  apply pullback.hom_ext ht
  apply (cancel_mono (((relativeCurveToBase incidencePoint t) ⁻¹ᵁ V).ι)).mp
  simpa only [Category.assoc, toOriginal] using ho

theorem curveMap_proper : IsProper (curveMap i V t) := by
  have := CycleQ2RelativeCurveNeighborhood.relativeCurveToBase_proper incidencePoint t
  unfold curveMap
  infer_instance

theorem joint_isClosedImmersion : IsClosedImmersion (joint i V t) := by
  apply (IsClosedImmersion.iff_isProper_and_mono _).mpr
  refine ⟨?_, joint_mono i V t⟩
  have : IsSeparated universalAmbientToBase := by
    unfold universalAmbientToBase weightedThreefoldToBase
    infer_instance
  have : IsProper (joint i V t ≫ pullback.fst _ _) := by
    rw [joint_toTime]
    exact curveMap_proper i V t
  exact IsProper.of_comp (joint i V t) (pullback.fst _ _)

end CycleQ2LiteralIncidenceRelativeEmbedding
end

#print axioms CycleQ2LiteralIncidenceRelativeEmbedding.joint_isClosedImmersion
