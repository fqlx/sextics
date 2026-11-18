import Proposal.GeometricLiteralTimeNormalizedCorrespondence

/-!
# The strict transform of the moving correspondence

Take the scheme-theoretic closure of the original time family inside the
proper correspondence over the normalized time base. Its original open is
dense and recovers the given family, including the map to the threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCorrespondenceStrictTransform

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralTimeCurveNormalization CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralTimeNormalizedCorrespondence
open CycleQ2IncidenceEtaleParameter (parameterScheme)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

local instance openImmersion_family : IsOpenImmersion (fromTimeFamily V t) :=
  MorphismProperty.of_isPullback (recovers_family V t) inferInstance

local instance quasiCompact_family : QuasiCompact (fromTimeFamily V t) := by
  let : QuasiCompact (openInclusion (timeOpen V)) :=
    inferInstanceAs (QuasiCompact (CycleQ2LiteralTimeCurveCompletion.inclusion (timeOpen V)).toNormalization)
  exact MorphismProperty.of_isPullback (recovers_family V t) inferInstance

abbrev Correspondence := (fromTimeFamily V t).image
abbrev inclusion : family V t ⟶ Correspondence V t := (fromTimeFamily V t).toImage
abbrev embedding := (fromTimeFamily V t).imageι

def baseProjection : Correspondence V t ⟶ Normalization (timeOpen V) := embedding V t ≫ toBase V t

def fixedProjection : Correspondence V t ⟶ FixedThreefold := embedding V t ≫ toFixed V t

instance : IsProper (baseProjection V t) := by unfold baseProjection embedding; infer_instance
instance : IsProper (fixedProjection V t) := by unfold fixedProjection embedding; infer_instance

instance : IsOpenImmersion (inclusion V t) :=
  inferInstanceAs (IsOpenImmersion (fromTimeFamily V t).toImage)

instance : IsDominant (inclusion V t) :=
  inferInstanceAs (IsDominant (fromTimeFamily V t).toImage)

@[reassoc (attr := simp)] theorem inclusion_toBase :
    inclusion V t ≫ baseProjection V t = projection V t ≫ openInclusion (timeOpen V) := by
  rw [baseProjection, ← Category.assoc, Scheme.Hom.toImage_imageι, fromTimeFamily_base]

@[reassoc (attr := simp)] theorem inclusion_toFixed :
    inclusion V t ≫ fixedProjection V t = q V t := by
  rw [fixedProjection, ← Category.assoc, Scheme.Hom.toImage_imageι, fromTimeFamily_fixed]

/-- The exact original family is the preimage of the original open, with
its full scheme structure, even after passing to the strict transform. -/
theorem recovery :
    IsPullback (projection V t) (inclusion V t) (openInclusion (timeOpen V)) (baseProjection V t) := by
  let h := recovers_family V t
  have w : projection V t ≫ openInclusion (timeOpen V) = inclusion V t ≫ baseProjection V t :=
    (inclusion_toBase V t).symm
  refine IsPullback.of_isLimit <| PullbackCone.IsLimit.mk w
    (fun s => h.lift s.fst (s.snd ≫ embedding V t) (s.condition.trans (Category.assoc ..).symm))
    (fun _ => h.lift_fst ..) ?_ ?_
  · intro s
    apply (cancel_mono (embedding V t)).mp
    rw [Category.assoc, Scheme.Hom.toImage_imageι, h.lift_snd]
  · intro s m hm₁ hm₂
    apply h.hom_ext
    · simpa only [h.lift_fst] using hm₁
    · rw [h.lift_snd, ← hm₂, Category.assoc, Scheme.Hom.toImage_imageι]

section Product
open CycleQ2LiteralTimeCorrespondenceCompletion (prBase prFixed fixedStructure)
open CycleQ2LiteralTimeCurveCompletion (structureMap)

private abbrev ProductOverCompletion := pullback (toCompletion (timeOpen V)) (prBase V)

private abbrev originalEmbedding := CycleQ2LiteralTimeCorrespondenceCompletion.embedding V t
private abbrev originalBase := CycleQ2LiteralTimeCorrespondenceCompletion.baseProjection V t

private def fullToProduct : CycleQ2LiteralTimeNormalizedCorrespondence.Family V t ⟶
    ProductOverCompletion V :=
  pullback.lift (toBase V t) (toOriginalClosure V t ≫ originalEmbedding V t)
    (by
      rw [Category.assoc]
      change pullback.fst _ _ ≫ toCompletion (timeOpen V) = pullback.snd _ _ ≫ originalBase V t
      exact pullback.condition)

private instance : IsClosedImmersion (fullToProduct V t) := by
  have H : IsPullback (fullToProduct V t ≫ pullback.fst _ _) (toOriginalClosure V t)
      (toCompletion (timeOpen V)) (originalEmbedding V t ≫ prBase V) := by
    rw [fullToProduct, pullback.lift_fst]
    exact .of_hasPullback _ _
  exact MorphismProperty.of_isPullback (H.of_right (pullback.lift_snd ..)
    (IsPullback.of_hasPullback _ _)).flip inferInstance

/-- The strict transform sits as a closed subscheme of the product of the
normalized time base with the specified fixed threefold over the complex point. -/
def intoProduct : Correspondence V t ⟶ pullback (toComplexPoint (timeOpen V)) fixedStructure :=
  embedding V t ≫ fullToProduct V t ≫ (pullbackRightPullbackFstIso
    (structureMap (timeOpen V)) fixedStructure (toCompletion (timeOpen V))).hom

instance intoProduct_closed : IsClosedImmersion (intoProduct V t) := by
  unfold intoProduct
  infer_instance

@[reassoc (attr := simp)] theorem intoProduct_base :
    intoProduct V t ≫ pullback.fst _ _ = baseProjection V t := by
  simp only [intoProduct, toComplexPoint, Category.assoc, pullbackRightPullbackFstIso_hom_fst,
    fullToProduct, pullback.lift_fst, baseProjection]

@[reassoc (attr := simp)] theorem intoProduct_fixed :
    intoProduct V t ≫ pullback.snd _ _ = fixedProjection V t := by
  simp only [intoProduct, toComplexPoint, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    fullToProduct, pullback.lift_snd_assoc, fixedProjection, toFixed,
    CycleQ2LiteralTimeCorrespondenceCompletion.fixedProjection, originalEmbedding]

end Product

theorem covers_normalized_base (hs : Function.Surjective (projection V t)) :
    Function.Surjective (baseProjection V t) := by
  let : Surjective (projection V t) := ⟨hs⟩
  let : IsDominant (inclusion V t ≫ baseProjection V t) := by
    rw [inclusion_toBase]
    infer_instance
  let := IsDominant.of_comp (inclusion V t) (baseProjection V t)
  exact (baseProjection V t).surjective

end CycleQ2LiteralTimeCorrespondenceStrictTransform
end

#print axioms CycleQ2LiteralTimeCorrespondenceStrictTransform.intoProduct_closed
#print axioms CycleQ2LiteralTimeCorrespondenceStrictTransform.recovery
#print axioms CycleQ2LiteralTimeCorrespondenceStrictTransform.covers_normalized_base
