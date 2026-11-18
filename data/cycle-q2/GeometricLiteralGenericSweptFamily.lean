import Proposal.GeometricLiteralIncidenceGenericModel
import Proposal.GeometricLiteralIncidenceRelativeCylinder

/-!
# The moving surface over the function field of the monic coefficients

The time open in the normalized generic model is the coefficient pullback
used to define the original incidence surface. Every marked neighborhood
therefore stays nonempty at the generic point. The selected proper curve
family surjects onto it and has nonempty image inside the generic sextic.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralGenericSweptFamily

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2IncidenceSeedFiberCover CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2LiteralIncidenceRelativeCylinder CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2LiteralIncidenceGenericModel (genericMorphism K TimeFiber)
open CycleQ2LiteralIncidenceRelativeNormalization (normalizedMap openInclusion open_over)

abbrev coefficient := genericMorphism ≫ toRaw

/-- This is the same generic time open in both constructions. -/
def timeIso (V : parameterScheme.Opens) : TimeFiber V ≅ Time coefficient V :=
  pullbackLeftPullbackSndIso genericMorphism (normalizedMap V) (openInclusion V) ≪≫
    pullback.congrHom (rfl : genericMorphism = genericMorphism) (open_over V) ≪≫
    pullbackRightPullbackFstIso toRaw (V.ι ≫ parameterToSextics) genericMorphism

theorem generic_time_nonempty (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) :
    Nonempty (Time coefficient V) := by
  let y := fixedToTime toRaw V seedPoint seedPoint_toRaw (seedLift V hV default)
  obtain ⟨x, _⟩ := CycleQ2LiteralIncidenceGenericModel.test_meets_generic V ⊤ ⟨y, trivial⟩
  exact ⟨(timeIso V).hom x⟩

/-- Every closed swept scheme of a surjective marked curve family has a
point on the genuine generic coefficient fibre. -/
theorem generic_support_nonempty (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)
    (t : Fin 3 → ℂ) (hs : Surjective (curveMap coefficient V t)) :
    Nonempty (relativeQ coefficient V t).image := by
  obtain ⟨y⟩ := generic_time_nonempty V hV
  obtain ⟨x, _⟩ := (curveMap coefficient V t).surjective y
  exact ⟨(relativeQ coefficient V t).toImage x⟩

end CycleQ2LiteralGenericSweptFamily
end

#print axioms CycleQ2LiteralGenericSweptFamily.timeIso
#print axioms CycleQ2LiteralGenericSweptFamily.generic_time_nonempty
#print axioms CycleQ2LiteralGenericSweptFamily.generic_support_nonempty
