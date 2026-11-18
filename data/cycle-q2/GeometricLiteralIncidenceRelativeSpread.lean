import Proposal.GeometricLiteralAbelJacobiTimeProjection
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Spreading the marked incidence correspondence over sextic coefficients

A neighborhood of the marked point in the original incidence scheme carries the
proper projective curve family. Its time direction is smooth over all sextic
coefficients. Base change to any irreducible coefficient scheme through the marked
sextic therefore gives a smooth relative surface with dense open image.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceRelativeSpread

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceTimeCurve CycleQ2RelativeConstantCurve
  CycleQ2IncidenceSeedFiberCover CycleQ2LiteralAbelJacobiTimeFamily

variable {B : Scheme} (i : B ⟶ sexticBase) (V : parameterScheme.Opens)

abbrev Time := pullback i (V.ι ≫ parameterToSextics)

def timeMap : Time i V ⟶ B := pullback.fst _ _

abbrev Surface (t : Fin 3 → ℂ) :=
  pullback (pullback.snd i (V.ι ≫ parameterToSextics)) ((relativeCurveToBase incidencePoint t) ∣_ V)

def curveMap (t : Fin 3 → ℂ) : Surface i V t ⟶ Time i V := pullback.fst _ _

variable (b : Spec (CommRingCat.of ℂ) ⟶ B) (hb : b ≫ i = seedSextic)

/-- The fixed-sextic time curve maps into the spread over its original marked coefficient. -/
def fixedToTime : (timeOpen V).toScheme ⟶ Time i V :=
  pullback.lift ((timeOpen V).ι ≫ toComplex ≫ b) (toIncidence ∣_ V) <| by
    simp only [Category.assoc, hb, ← Category.assoc (toIncidence ∣_ V), morphismRestrict_ι]
    simpa only [Category.assoc, timeOpen, toComplex, toIncidence] using congrArg (fun f => (timeOpen V).ι ≫ f)
      (pullback.condition (f := seedSextic) (g := parameterToSextics))

@[reassoc (attr := simp)] theorem fixedToTime_fst :
    fixedToTime i V b hb ≫ timeMap i V = (timeOpen V).ι ≫ toComplex ≫ b := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fixedToTime_snd :
    fixedToTime i V b hb ≫ pullback.snd i (V.ι ≫ parameterToSextics) = toIncidence ∣_ V :=
  pullback.lift_snd _ _ _

theorem timeMap_smooth : SmoothOfRelativeDimension 1 (timeMap i V) := by
  have := parameterToSextics_smooth_relative_one
  let _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_fst _ _ (smoothOfRelativeDimension_comp 0 1 V.ι parameterToSextics)

/-- Every nonempty Zariski neighborhood in the time family meets the inverse image
of each nonempty open of an irreducible coefficient space. -/
theorem timeOpen_meets_coefficients [IrreducibleSpace B] (W : (Time i V).Opens)
    (hW : (W : Set (Time i V)).Nonempty) (U : B.Opens) (hU : (U : Set B).Nonempty) :
    ∃ x ∈ W, timeMap i V x ∈ U := by
  have := timeMap_smooth i V
  have : Smooth (timeMap i V) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨_, ⟨x, hx, rfl⟩, hxU⟩ := nonempty_preirreducible_inter
    ((timeMap i V).isOpenMap _ W.isOpen) U.isOpen (hW.image _) hU
  exact ⟨x, hx, hxU⟩

include b hb in
/-- The same section vector gives a smooth relative surface after any pointed base change.
Its curve projection is proper and surjective and its image in the coefficients is dense. -/
theorem spread_of_independent [IrreducibleSpace B] (t : Fin 3 → ℂ)
    (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      SmoothOfRelativeDimension 1 (timeMap i V) ∧
      SmoothOfRelativeDimension 1 (curveMap i V t) ∧
      SmoothOfRelativeDimension 2 (curveMap i V t ≫ timeMap i V) ∧
      IsProper (curveMap i V t) ∧ Surjective (curveMap i V t) ∧
      IsOpen (Set.range (timeMap i V)) ∧ IsDominant (timeMap i V) ∧
      IsDominant (curveMap i V t ≫ timeMap i V) := by
  obtain ⟨W, hW, hcurve, hproper, hsurj⟩ :=
    CycleQ2LiteralAbelJacobiSeedLiftDimension.dimension_one_neighborhood_of_seedMinorCover t
      (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t hi)
  have : Surjective ((relativeCurveToBase incidencePoint t) ∣_ W) := ⟨hsurj⟩
  let _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hπ : SmoothOfRelativeDimension 1 (curveMap i W t) := MorphismProperty.pullback_fst _ _ hcurve
  have hτ := timeMap_smooth i W
  have : Smooth (timeMap i W) := SmoothOfRelativeDimension.smooth 1 _
  have hne : Nonempty (Time i W) := ⟨fixedToTime i W b hb (seedLift W hW default)⟩
  have hdom : IsDominant (timeMap i W) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ (timeMap i W).isOpenMap⟩
  have hsur : Surjective (curveMap i W t) := by unfold curveMap; infer_instance
  refine ⟨W, hW, hτ, hπ, smoothOfRelativeDimension_comp 1 1 _ _, ?_, hsur,
    (timeMap i W).isOpenMap.isOpen_range, hdom, inferInstance⟩
  unfold curveMap
  infer_instance

end CycleQ2LiteralIncidenceRelativeSpread
end

#print axioms CycleQ2LiteralIncidenceRelativeSpread.spread_of_independent
