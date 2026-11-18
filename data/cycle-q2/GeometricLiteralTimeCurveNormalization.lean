import Proposal.GeometricLiteralTimeCurveCompletion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Relative normalization of the actual projective time-curve closure

Zariski's main theorem makes the original parameter open a dense open in
the relative normalization of its projective closure. The map back to that
closure is both integral and surjective. The smooth parameter germ and
its nonconstant dual-number point agree with the original ones.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCurveNormalization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CycleQ2LiteralIncidenceTimeCurve
  CycleQ2LiteralTimeCurveCompletion

variable (U : Curve.Opens)

abbrev Normalization := (inclusion U).normalization

def openInclusion : U.toScheme ⟶ Normalization U := (inclusion U).toNormalization

def toCompletion : Normalization U ⟶ Completion U := (inclusion U).fromNormalization

def toComplexPoint : Normalization U ⟶ Spec (CommRingCat.of ℂ) :=
  toCompletion U ≫ structureMap U

instance : IsOpenImmersion (openInclusion U) :=
  inferInstanceAs (IsOpenImmersion (inclusion U).toNormalization)

instance : IsDominant (openInclusion U) :=
  inferInstanceAs (IsDominant (inclusion U).toNormalization)

instance : IsIntegralHom (toCompletion U) :=
  inferInstanceAs (IsIntegralHom (inclusion U).fromNormalization)

@[reassoc (attr := simp)] theorem inclusion_toCompletion :
    openInclusion U ≫ toCompletion U = inclusion U :=
  (inclusion U).toNormalization_fromNormalization

instance : IsDominant (toCompletion U) := by
  let : IsDominant (openInclusion U ≫ toCompletion U) := by
    rw [inclusion_toCompletion]
    infer_instance
  exact IsDominant.of_comp (openInclusion U) (toCompletion U)

/-- Over the entire original open, base change of the comparison recovers
that open isomorphically, including its scheme structure. -/
theorem toCompletion_over_open_isIso :
    IsIso (pullback.snd (toCompletion U) (inclusion U)) := by
  let f := inclusion U
  change IsIso (pullback.snd f.fromNormalization f)
  rw [← isIso_comp_left_iff (f.normalizationPullback f), f.normalizationPullback_snd,
    ← isIso_comp_left_iff (pullback.snd f f).toNormalization,
    Scheme.Hom.toNormalization_fromNormalization]
  infer_instance

theorem toCompletion_surjective : Surjective (toCompletion U) := inferInstance

theorem toComplexPoint_universallyClosed : UniversallyClosed (toComplexPoint U) := by
  unfold toComplexPoint
  infer_instance

/-- On this normalization, the additional requirement for a finite map to
the projective closure is local finite type. -/
theorem toCompletion_finite_iff :
    IsFinite (toCompletion U) ↔ LocallyOfFiniteType (toCompletion U) := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact and_iff_right inferInstance

theorem toComplexPoint_proper_of_locallyOfFiniteType [LocallyOfFiniteType (toCompletion U)] :
    IsProper (toComplexPoint U) := by
  let : IsFinite (toCompletion U) := (toCompletion_finite_iff U).mpr inferInstance
  unfold toComplexPoint
  infer_instance

@[reassoc (attr := simp)] theorem inclusion_over :
    openInclusion U ≫ toComplexPoint U = U.ι ≫ toComplex := by
  rw [toComplexPoint, inclusion_toCompletion_assoc, CycleQ2LiteralTimeCurveCompletion.inclusion_over]

/-- Every original open of the curve is a smooth one-dimensional open
of its normalization over the same coefficient field. -/
theorem smooth_on_original_open :
    SmoothOfRelativeDimension 1 (openInclusion U ≫ toComplexPoint U) := by
  rw [inclusion_over]
  have := smooth_parameter_curve
  exact smoothOfRelativeDimension_comp 0 1 _ _

/-- Unequal infinitesimal points in the original open stay unequal. -/
theorem preserves_distinct_maps {T : Scheme} {a b : T ⟶ U.toScheme} (h : a ≠ b) :
    a ≫ openInclusion U ≠ b ≫ openInclusion U :=
  fun hab => h ((cancel_mono (openInclusion U)).mp hab)

def wholeCurveInclusion : Curve ⟶ Normalization ⊤ :=
  Curve.topIso.inv ≫ openInclusion ⊤

/-- The retained nonconstant dual-number point stays nonconstant on the
relative normalization of the entire time curve's projective closure. -/
theorem tangent_nonconstant :
    timeTangent ≫ wholeCurveInclusion ≠ structureDual ≫ seed ≫ wholeCurveInclusion := by
  have : Mono wholeCurveInclusion := by unfold wholeCurveInclusion; infer_instance
  intro h
  apply timeTangent_nonconstant
  exact (cancel_mono wholeCurveInclusion).mp (by simpa only [Category.assoc] using h)

end CycleQ2LiteralTimeCurveNormalization
end

#print axioms CycleQ2LiteralTimeCurveNormalization.toCompletion_over_open_isIso
#print axioms CycleQ2LiteralTimeCurveNormalization.toCompletion_surjective
#print axioms CycleQ2LiteralTimeCurveNormalization.smooth_on_original_open
#print axioms CycleQ2LiteralTimeCurveNormalization.tangent_nonconstant
#print axioms CycleQ2LiteralTimeCurveNormalization.toComplexPoint_universallyClosed
#print axioms CycleQ2LiteralTimeCurveNormalization.toComplexPoint_proper_of_locallyOfFiniteType
