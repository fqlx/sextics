import Proposal.GeometricLiteralTimeNormalizationFinite
import Proposal.GeometricLiteralTimeFamilyRecovery

/-!
# The moving correspondence over the finite normalized time base

Pull the proper correspondence back to the finite normalization of the
parameter base. Both projections stay proper, and the restriction to the
original parameter open is the original moving family with its given map
to the fixed threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeNormalizedCorrespondence

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralTimeCorrespondenceCompletion CycleQ2LiteralTimeCurveNormalization
  CycleQ2LiteralIncidenceCylinderMap
open CycleQ2IncidenceEtaleParameter (parameterScheme)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev Family := pullback (toCompletion (timeOpen V)) (baseProjection V t)

abbrev toBase : Family V t ⟶ Normalization (timeOpen V) := pullback.fst _ _
abbrev toOriginalClosure : Family V t ⟶ Correspondence V t := pullback.snd _ _

def toFixed : Family V t ⟶ FixedThreefold := toOriginalClosure V t ≫ fixedProjection V t

instance : IsProper (toBase V t) := by unfold toBase; infer_instance

instance : IsProper (toFixed V t) := by unfold toFixed toOriginalClosure; infer_instance

def fromTimeFamily : family V t ⟶ Family V t :=
  pullback.lift (projection V t ≫ openInclusion (timeOpen V)) (fromFamily V t) (by simp)

@[reassoc (attr := simp)] theorem fromTimeFamily_base :
    fromTimeFamily V t ≫ toBase V t = projection V t ≫ openInclusion (timeOpen V) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fromTimeFamily_original :
    fromTimeFamily V t ≫ toOriginalClosure V t = fromFamily V t :=
  pullback.lift_snd _ _ _

theorem fromTimeFamily_fixed : fromTimeFamily V t ≫ toFixed V t = q V t := by
  simp only [toFixed, fromTimeFamily_original_assoc, fromFamily_toFixed]

/-- The open part of the normalized proper correspondence is the given
family, with its scheme structure and its original two maps. -/
theorem recovers_family :
    IsPullback (projection V t) (fromTimeFamily V t) (openInclusion (timeOpen V)) (toBase V t) := by
  have h : IsPullback (projection V t) (fromTimeFamily V t ≫ toOriginalClosure V t)
      (openInclusion (timeOpen V) ≫ toCompletion (timeOpen V)) (baseProjection V t) := by
    rw [fromTimeFamily_original, inclusion_toCompletion]
    exact CycleQ2LiteralTimeFamilyRecovery.timeOpen_pullback V t
  exact h.of_bot (fromTimeFamily_base V t).symm (.of_hasPullback _ _)

theorem surjective (h : Function.Surjective (projection V t)) : Function.Surjective (toBase V t) := by
  let : Surjective (baseProjection V t) := ⟨baseProjection_surjective V t h⟩
  exact (pullback.fst (toCompletion (timeOpen V)) (baseProjection V t)).surjective

end CycleQ2LiteralTimeNormalizedCorrespondence

#print axioms CycleQ2LiteralTimeNormalizedCorrespondence.recovers_family
#print axioms CycleQ2LiteralTimeNormalizedCorrespondence.fromTimeFamily_fixed
#print axioms CycleQ2LiteralTimeNormalizedCorrespondence.surjective
