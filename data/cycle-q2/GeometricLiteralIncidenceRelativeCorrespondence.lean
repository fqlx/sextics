import Proposal.GeometricLiteralIncidenceRelativeCompletion
import Proposal.GeometricLiteralIncidenceRelativeEmbedding
import Proposal.GeometricLiteralRelativeAmbientProper
import Proposal.GeometricRelativeGraphClosure

/-!
# The proper correspondence over the full normalized sextic coefficient space

Close the original family of embedded curves in the product of the proper
relative time compactification and the universal threefold. The original
family is its restriction to the dense time open. The marked seed curve and
its dual-number deformation are recovered by scheme-theoretic pullback.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LiteralIncidenceRelativeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceRelativeCylinder
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralIncidenceRelativeCompletion
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2LiteralIncidenceNormalizedSlice (toRaw monicBase seedPoint seedPoint_toRaw)
open CycleQ2LiteralIncidenceCylinderMap (universalAmbientToBase)

abbrev ambientStructure : ambient toRaw ⟶ monicBase :=
  pullback.fst toRaw universalAmbientToBase

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

private abbrev openGraph := CycleQ2LiteralIncidenceRelativeEmbedding.joint toRaw V t

abbrev Product := pullback (structureMap V) ambientStructure

abbrev Correspondence :=
  CycleQ2RelativeGraphClosure.Closure (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

/-- The scheme-theoretic graph closure in the relative product. -/
abbrev embedding : Correspondence V t ⟶ Product V :=
  CycleQ2RelativeGraphClosure.embedding (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

abbrev fromSurface : Surface toRaw V t ⟶ Correspondence V t :=
  CycleQ2RelativeGraphClosure.toClosure (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

abbrev timeProjection : Correspondence V t ⟶ Completion V :=
  CycleQ2RelativeGraphClosure.timeProjection (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

abbrev ambientProjection : Correspondence V t ⟶ ambient toRaw :=
  CycleQ2RelativeGraphClosure.targetProjection (timeMap toRaw V) (structureMap V) ambientStructure
    (inclusion V) (inclusion_over V) (openGraph V t)

instance : IsProper (ambientProjection V t) :=
  inferInstanceAs (IsProper (CycleQ2RelativeGraphClosure.targetProjection _ _ _ _ _ _))

instance : IsProper (timeProjection V t) := by
  let : IsProper ambientStructure := CycleQ2LiteralRelativeAmbientProper.ambient_proper toRaw
  exact inferInstanceAs (IsProper (CycleQ2RelativeGraphClosure.timeProjection _ _ _ _ _ _))

@[reassoc (attr := simp)]
theorem fromSurface_toTime : fromSurface V t ≫ timeProjection V t = curveMap toRaw V t ≫ inclusion V := by
  simpa only [openGraph, CycleQ2LiteralIncidenceRelativeEmbedding.joint_toTime_assoc, fromSurface, timeProjection] using
    CycleQ2RelativeGraphClosure.toClosure_timeProjection (timeMap toRaw V) (structureMap V)
      ambientStructure (inclusion V) (inclusion_over V) (openGraph V t)

@[reassoc (attr := simp)]
theorem fromSurface_toAmbient : fromSurface V t ≫ ambientProjection V t = relativeQ toRaw V t := by
  simpa only [openGraph, CycleQ2LiteralIncidenceRelativeEmbedding.joint_toAmbient, fromSurface, ambientProjection] using
    CycleQ2RelativeGraphClosure.toClosure_targetProjection (timeMap toRaw V) (structureMap V)
      ambientStructure (inclusion V) (inclusion_over V) (openGraph V t)

/-- Restricting the proper relative correspondence along the dense time open recovers its
original scheme of embedded curves over all normalized coefficients. -/
theorem timeOpen_pullback :
    IsPullback (curveMap toRaw V t) (fromSurface V t) (inclusion V) (timeProjection V t) := by
  let : IsClosedImmersion (openGraph V t) :=
    CycleQ2LiteralIncidenceRelativeEmbedding.joint_isClosedImmersion toRaw V t
  simpa only [openGraph, CycleQ2LiteralIncidenceRelativeEmbedding.joint_toTime, fromSurface, timeProjection] using
    CycleQ2RelativeGraphClosure.recovery (timeMap toRaw V) (structureMap V) ambientStructure
      (inclusion V) (inclusion_over V) (openGraph V t)

instance : IsOpenImmersion (fromSurface V t) :=
  MorphismProperty.of_isPullback (timeOpen_pullback V t) inferInstance

instance : IsDominant (fromSurface V t) := by
  let : IsClosedImmersion (openGraph V t) :=
    CycleQ2LiteralIncidenceRelativeEmbedding.joint_isClosedImmersion toRaw V t
  exact inferInstanceAs (IsDominant (CycleQ2RelativeGraphClosure.toClosure _ _ _ _ _ _))

/-- The fixed surface of moving curves is the pullback over its original marked time curve. -/
theorem markedTime_pullback :
    IsPullback (projection V t)
      (fixedToSurface toRaw V t seedPoint seedPoint_toRaw ≫ fromSurface V t)
      (fixedToTime toRaw V seedPoint seedPoint_toRaw ≫ inclusion V) (timeProjection V t) :=
  (fixed_curve_square toRaw V t seedPoint seedPoint_toRaw).paste_vert (timeOpen_pullback V t)

@[reassoc (attr := simp)]
theorem markedTime_toAmbient :
    (fixedToSurface toRaw V t seedPoint seedPoint_toRaw ≫ fromSurface V t) ≫ ambientProjection V t =
      CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫ fixedToAmbient toRaw seedPoint seedPoint_toRaw := by
  rw [Category.assoc, fromSurface_toAmbient, fixed_q]

variable {Z : Scheme} (z : Z ⟶ (timeOpen V).toScheme)

/-- Base change of the proper correspondence along a marked time germ, including the dual
numbers, with the same embedded-curve scheme as the original open family. -/
def markedFiberIso :
    pullback z (projection V t) ≅ pullback
      (z ≫ fixedToTime toRaw V seedPoint seedPoint_toRaw ≫ inclusion V) (timeProjection V t) :=
  ((IsPullback.of_hasPullback z (projection V t)).paste_vert (markedTime_pullback V t)).isoPullback

@[reassoc (attr := simp)]
theorem markedFiberIso_fst :
    (markedFiberIso V t z).hom ≫ pullback.fst _ (timeProjection V t) = pullback.fst z (projection V t) :=
  ((IsPullback.of_hasPullback z (projection V t)).paste_vert (markedTime_pullback V t)).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem markedFiberIso_snd :
    (markedFiberIso V t z).hom ≫ pullback.snd _ (timeProjection V t) =
      pullback.snd z (projection V t) ≫ fixedToSurface toRaw V t seedPoint seedPoint_toRaw ≫
        fromSurface V t :=
  ((IsPullback.of_hasPullback z (projection V t)).paste_vert (markedTime_pullback V t)).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem markedFiberIso_toAmbient :
    (markedFiberIso V t z).hom ≫ pullback.snd _ (timeProjection V t) ≫ ambientProjection V t =
      pullback.snd z (projection V t) ≫ CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫
        fixedToAmbient toRaw seedPoint seedPoint_toRaw := by
  simp only [markedFiberIso_snd_assoc, fromSurface_toAmbient, fixed_q]

/-- The marked fibre of the relative proper correspondence is the original plane-section curve. -/
def seedFiberIso (hV : seedBasePoint ∈ V) :=
  CycleQ2LiteralAbelJacobiTimeProjection.seedIso V t hV ≪≫ markedFiberIso V t (seedLift V hV)

/-- Its pullback at the original nonconstant dual-number tangent is the original embedded
first-order family. -/
def firstOrderFiberIso (hV : seedBasePoint ∈ V) :=
  firstOrderIso V t hV ≪≫ markedFiberIso V t (tangentLift V hV)

/-- The recovered seed curve has its original projection into the fixed threefold
over the marked coefficient point. -/
theorem seedFiberIso_toAmbient (hV : seedBasePoint ∈ V) :
    (seedFiberIso V t hV).hom ≫ pullback.snd _ (timeProjection V t) ≫ ambientProjection V t =
      (CycleQ2LiteralIncidenceTimeFamily.seedIso t).hom ≫ pullback.snd _ _ ≫
        CycleQ2LiteralIncidenceCylinderMap.toFixedThreefold t ≫ fixedToAmbient toRaw seedPoint seedPoint_toRaw := by
  simp only [seedFiberIso, Iso.trans_hom, Category.assoc, markedFiberIso_toAmbient,
    CycleQ2LiteralAbelJacobiTimeProjection.seed_to_q_assoc]

/-- The recovered first-order curve maps into the universal threefold via its original
embedded map into the fixed threefold. -/
theorem firstOrderFiberIso_toAmbient (hV : seedBasePoint ∈ V) :
    (firstOrderFiberIso V t hV).hom ≫ pullback.snd _ (timeProjection V t) ≫ ambientProjection V t =
      (CycleQ2LiteralIncidenceTimeFamily.firstOrderIso t).hom ≫ pullback.snd _ _ ≫
        CycleQ2LiteralIncidenceCylinderMap.toFixedThreefold t ≫ fixedToAmbient toRaw seedPoint seedPoint_toRaw := by
  simp only [firstOrderFiberIso, Iso.trans_hom, Category.assoc, markedFiberIso_toAmbient,
    CycleQ2LiteralAbelJacobiTimeProjection.firstOrder_to_q_assoc]

/-- Passing to the compactified full time family preserves the nonconstant tangent of
the marked moving curve. -/
theorem tangent_nonconstant (hV : seedBasePoint ∈ V) :
    relativeTangent toRaw V seedPoint seedPoint_toRaw hV ≫ inclusion V ≠
      CycleQ2LiteralIncidenceTimeCurve.structureDual ≫ seedLift V hV ≫
        fixedToTime toRaw V seedPoint seedPoint_toRaw ≫ inclusion V := by
  intro he
  apply CycleQ2LiteralIncidenceRelativeCylinder.tangent_nonconstant toRaw V seedPoint seedPoint_toRaw hV
  exact (cancel_mono (inclusion V)).mp (by simpa only [Category.assoc] using he)

theorem timeProjection_surjective (hs : Surjective (curveMap toRaw V t)) :
    Function.Surjective (timeProjection V t) := by
  let : IsDominant (fromSurface V t ≫ timeProjection V t) := by
    rw [fromSurface_toTime]
    infer_instance
  let := IsDominant.of_comp (fromSurface V t) (timeProjection V t)
  exact (timeProjection V t).surjective

/-- Every independent section triple supplies a proper relative correspondence covering its
proper time compactification and recovering the marked fixed-sextic surface on the time open. -/
theorem relative_correspondence_of_independent (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      IsProper (timeProjection V t ≫ structureMap V) ∧
      Function.Surjective (timeProjection V t) ∧ Function.Surjective (timeProjection V t ≫ structureMap V) ∧
      IsProper (ambientProjection V t) ∧
      IsOpenImmersion (fromSurface V t) ∧ IsDominant (fromSurface V t) ∧
      IsPullback (curveMap toRaw V t) (fromSurface V t) (inclusion V) (timeProjection V t) ∧
      IsPullback (projection V t) (fixedToSurface toRaw V t seedPoint seedPoint_toRaw ≫ fromSurface V t)
        (fixedToTime toRaw V seedPoint seedPoint_toRaw ≫ inclusion V) (timeProjection V t) := by
  obtain ⟨V, hV, _, _, _, hs, _, hbase⟩ := exists_surjective_completion t hi
  have htime := timeProjection_surjective V t hs
  exact ⟨V, hV, inferInstance, htime, (structureMap V).surjective.comp htime, inferInstance, inferInstance,
    inferInstance, timeOpen_pullback V t, markedTime_pullback V t⟩

end CycleQ2LiteralIncidenceRelativeCorrespondence

#print axioms CycleQ2LiteralIncidenceRelativeCorrespondence.relative_correspondence_of_independent
#print axioms CycleQ2LiteralIncidenceRelativeCorrespondence.firstOrderFiberIso
