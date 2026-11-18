import Proposal.GeometricLiteralIncidenceRelativeSpread
import Proposal.GeometricLiteralIncidenceNormalizedSlice
import Proposal.GeometricAffineProjectiveCompletionChart
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A relative projective closure over the normalized sextic base

The finite-type incidence algebra embeds the parameter scheme in a complex
affine space. The monic slice of its marked open thus embeds into a projective
space over the normalized coefficient scheme. Its scheme-theoretic image
compactifies the entire time open over that base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceRelativeCompletion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2AffineProjectiveCompletionChart CycleQ2IncidenceSeedFiberCover

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

private def coefficients : ℂ →+* ParameterAlgebra :=
  sexticToParameter.comp (algebraMap ℂ SexticRing)

private local instance : Algebra ℂ ParameterAlgebra := coefficients.toAlgebra

private theorem finiteType : Algebra.FiniteType ℂ ParameterAlgebra := by
  have h : sexticToParameter.FiniteType :=
    RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType SexticRing ParameterAlgebra)
  exact h.comp (RingHom.finiteType_algebraMap.mpr inferInstance)

private theorem exists_presentation :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ParameterAlgebra), Function.Surjective φ :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.mp finiteType

abbrev Axes := Fin exists_presentation.choose

private def presentation : MvPolynomial Axes ℂ →ₐ[ℂ] ParameterAlgebra :=
  exists_presentation.choose_spec.choose

private def intoProjective : parameterScheme ⟶ projectiveSpace Axes :=
  Spec.map (CommRingCat.ofHom presentation.toRingHom) ≫ affineChart Axes

private instance : IsImmersion intoProjective := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom presentation.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ exists_presentation.choose_spec.choose_spec
  unfold intoProjective
  infer_instance

private theorem intoProjective_over :
    intoProjective ≫ projectiveToComplex Axes =
      parameterToSextics ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ SexticRing)) := by
  rw [intoProjective, Category.assoc, affineChart_over, parameterToSextics, ← Spec.map_comp,
    ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext presentation.comp_algebraMap)

abbrev ProjectiveBundle := pullback toComplex (projectiveToComplex Axes)

variable (V : parameterScheme.Opens)

/-- The joint coefficient and projective coordinate map of the actual normalized time curve. -/
def graph : Time toRaw V ⟶ ProjectiveBundle :=
  pullback.lift (timeMap toRaw V) (pullback.snd _ _ ≫ V.ι ≫ intoProjective) <| by
    rw [Category.assoc, Category.assoc, intoProjective_over, ← toRaw_over]
    simpa only [timeMap, Category.assoc] using pullback.condition_assoc
      (f := toRaw) (g := V.ι ≫ parameterToSextics)
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ SexticRing)))

instance : IsImmersion (graph V) := by
  have : IsImmersion (graph V ≫ pullback.snd toComplex (projectiveToComplex Axes)) := by
    rw [graph, pullback.lift_snd]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.snd toComplex (projectiveToComplex Axes))

instance : QuasiCompact (graph V) := by
  let _ := finiteType
  let _ := Algebra.FiniteType.isNoetherianRing ℂ ParameterAlgebra
  have : NoetherianSpace parameterScheme :=
    inferInstanceAs (NoetherianSpace (Spec (CommRingCat.of ParameterAlgebra)))
  have : NoetherianSpace V.toScheme := NoetherianSpace.set (V : Set parameterScheme)
  have : NoetherianSpace (Time toRaw V) :=
    (pullback.snd toRaw (V.ι ≫ parameterToSextics)).isClosedEmbedding.isInducing.noetherianSpace
  infer_instance

abbrev Completion := (graph V).image

def inclusion : Time toRaw V ⟶ Completion V := (graph V).toImage

def structureMap : Completion V ⟶ monicBase :=
  (graph V).imageι ≫ pullback.fst toComplex (projectiveToComplex Axes)

instance : IsProper (structureMap V) := by
  have := projectiveToComplex_proper Axes
  unfold structureMap
  infer_instance

instance : IsOpenImmersion (inclusion V) := inferInstanceAs (IsOpenImmersion (graph V).toImage)

instance : IsDominant (inclusion V) := inferInstanceAs (IsDominant (graph V).toImage)

instance : QuasiCompact (inclusion V) := inferInstanceAs (QuasiCompact (graph V).toImage)

@[reassoc (attr := simp)] theorem inclusion_over :
    inclusion V ≫ structureMap V = timeMap toRaw V := by
  rw [inclusion, structureMap, ← Category.assoc, Scheme.Hom.toImage_imageι, graph, pullback.lift_fst]

/-- The marked time neighborhood in the proper closure is smooth of relative dimension one. -/
theorem smooth_time_neighborhood :
    SmoothOfRelativeDimension 1 (inclusion V ≫ structureMap V) := by
  rw [inclusion_over]
  exact timeMap_smooth _ _

/-- The same marked vector gives a proper time completion surjective over the full monic chart. -/
theorem exists_surjective_completion (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      SmoothOfRelativeDimension 1 (curveMap toRaw V t) ∧
      SmoothOfRelativeDimension 2 (curveMap toRaw V t ≫ timeMap toRaw V) ∧
      IsProper (curveMap toRaw V t) ∧ Surjective (curveMap toRaw V t) ∧
      IsDominant (timeMap toRaw V) ∧ Surjective (structureMap V) := by
  have : IrreducibleSpace monicBase :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  obtain ⟨W, hW, _, hπ, hS, hp, hs, _, hdom, _⟩ :=
    spread_of_independent toRaw seedPoint seedPoint_toRaw t hi
  have : IsDominant (inclusion W ≫ structureMap W) := by
    rw [inclusion_over]
    exact hdom
  have := IsDominant.of_comp (inclusion W) (structureMap W)
  exact ⟨W, hW, hπ, hS, hp, hs, hdom,
    surjective_of_isDominant_of_isClosed_range _ (structureMap W).isClosedMap.isClosed_range⟩

end CycleQ2LiteralIncidenceRelativeCompletion
end

#print axioms CycleQ2LiteralIncidenceRelativeCompletion.inclusion_over
#print axioms CycleQ2LiteralIncidenceRelativeCompletion.exists_surjective_completion
