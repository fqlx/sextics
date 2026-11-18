import Proposal.GeometricLiteralIncidenceRelativeSpread

/-!
# The correspondence projection and tangent on the relative incidence spread

The second projection uses the original embedded incidence curve over the universal
sextic. The marked coefficient fibre is the original pointed family, including
its map to the fixed threefold and its nonconstant dual-number tangent.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceRelativeCylinder

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve CycleQ2IncidenceFirstOrder
  CycleQ2LiteralIncidenceTimeCurve CycleQ2RelativeConstantCurve CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceFamilyContainment CycleQ2FirstOrderCurve

variable {B : Scheme} (i : B ⟶ sexticBase) (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev ambient := pullback i universalAmbientToBase

def toOriginal : Surface i V t ⟶ relativeCurve incidencePoint t :=
  pullback.snd _ ((relativeCurveToBase incidencePoint t) ∣_ V) ≫
    ((relativeCurveToBase incidencePoint t) ⁻¹ᵁ V).ι

theorem over_coefficients :
    (curveMap i V t ≫ timeMap i V) ≫ i = (toOriginal i V t ≫ originalToAmbient t) ≫ universalAmbientToBase := by
  let f := relativeCurveToBase incidencePoint t
  have hT : timeMap i V ≫ i = pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι ≫ parameterToSextics :=
    pullback.condition
  have hS : curveMap i V t ≫ pullback.snd i (V.ι ≫ parameterToSextics) =
      pullback.snd _ (f ∣_ V) ≫ (f ∣_ V) := pullback.condition
  rw [Category.assoc, hT, ← Category.assoc (curveMap i V t), hS, Category.assoc, Category.assoc,
    original_over_coefficients]
  change pullback.snd _ (f ∣_ V) ≫ (f ∣_ V) ≫ V.ι ≫ parameterToSextics =
    (pullback.snd _ (f ∣_ V) ≫ (f ⁻¹ᵁ V).ι) ≫ f ≫ parameterToSextics
  rw [morphismRestrict_ι_assoc, Category.assoc]

def relativeQ : Surface i V t ⟶ ambient i :=
  pullback.lift (curveMap i V t ≫ timeMap i V) (toOriginal i V t ≫ originalToAmbient t)
    (over_coefficients i V t)

@[reassoc (attr := simp)] theorem relativeQ_fst :
    relativeQ i V t ≫ pullback.fst i universalAmbientToBase = curveMap i V t ≫ timeMap i V := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem relativeQ_snd :
    relativeQ i V t ≫ pullback.snd i universalAmbientToBase = toOriginal i V t ≫ originalToAmbient t :=
  pullback.lift_snd _ _ _

variable (b : Spec (CommRingCat.of ℂ) ⟶ B) (hb : b ≫ i = seedSextic)

def fixedToAmbient : FixedThreefold ⟶ ambient i :=
  pullback.lift (pullback.fst seedSextic universalAmbientToBase ≫ b) (pullback.snd _ _) <| by
    rw [Category.assoc, hb, pullback.condition]

theorem fixed_ambient_square :
    IsPullback (pullback.fst seedSextic universalAmbientToBase) (fixedToAmbient i b hb)
      b (pullback.fst i universalAmbientToBase) := by
  have h : IsPullback (pullback.fst seedSextic universalAmbientToBase)
      (fixedToAmbient i b hb ≫ pullback.snd i universalAmbientToBase) (b ≫ i)
      universalAmbientToBase := by
    rw [fixedToAmbient, pullback.lift_snd, hb]
    exact IsPullback.of_hasPullback ..
  exact h.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback ..)

def fixedToSurface : family V t ⟶ Surface i V t :=
  pullback.lift (projection V t ≫ fixedToTime i V b hb) (pullback.snd _ _) <| by
    rw [Category.assoc, fixedToTime_snd]
    exact pullback.condition

@[reassoc (attr := simp)] theorem fixedToSurface_fst :
    fixedToSurface i V t b hb ≫ curveMap i V t = projection V t ≫ fixedToTime i V b hb := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fixedToSurface_snd :
    fixedToSurface i V t b hb ≫ pullback.snd _ ((relativeCurveToBase incidencePoint t) ∣_ V) =
      pullback.snd _ _ := pullback.lift_snd _ _ _

theorem fixed_time_square :
    IsPullback ((timeOpen V).ι ≫ toComplex) (fixedToTime i V b hb) b (timeMap i V) := by
  have h₀ := (isPullback_morphismRestrict toIncidence V).flip.paste_horiz
    (IsPullback.of_hasPullback seedSextic parameterToSextics)
  have h : IsPullback ((timeOpen V).ι ≫ toComplex)
      (fixedToTime i V b hb ≫ pullback.snd i (V.ι ≫ parameterToSextics)) (b ≫ i)
      (V.ι ≫ parameterToSextics) := by rw [fixedToTime_snd, hb]; exact h₀
  exact h.of_bot (by rw [fixedToTime_fst, Category.assoc]) (IsPullback.of_hasPullback ..)

theorem fixed_curve_square :
    IsPullback (projection V t) (fixedToSurface i V t b hb) (fixedToTime i V b hb) (curveMap i V t) := by
  have h : IsPullback (projection V t)
      (fixedToSurface i V t b hb ≫ pullback.snd _ ((relativeCurveToBase incidencePoint t) ∣_ V))
      (fixedToTime i V b hb ≫ pullback.snd i (V.ι ≫ parameterToSextics))
      ((relativeCurveToBase incidencePoint t) ∣_ V) := by
    rw [fixedToSurface_snd, fixedToTime_snd]
    exact IsPullback.of_hasPullback ..
  exact h.of_bot (fixedToSurface_fst i V t b hb).symm (IsPullback.of_hasPullback ..)

theorem fixed_surface_square :
    IsPullback (projection V t ≫ (timeOpen V).ι ≫ toComplex) (fixedToSurface i V t b hb)
      b (curveMap i V t ≫ timeMap i V) :=
  (fixed_curve_square i V t b hb).paste_horiz (fixed_time_square i V b hb)

theorem fixed_q :
    fixedToSurface i V t b hb ≫ relativeQ i V t =
      CycleQ2LiteralAbelJacobiTimeProjection.q V t ≫ fixedToAmbient i b hb := by
  apply pullback.hom_ext
  · simp only [fixedToAmbient, Category.assoc, relativeQ_fst, fixedToSurface_fst_assoc,
      fixedToTime_fst, pullback.lift_fst, CycleQ2LiteralAbelJacobiTimeProjection.q_overComplex_assoc]
  · simp only [fixedToAmbient, Category.assoc, relativeQ_snd, toOriginal, fixedToSurface_snd_assoc,
      pullback.lift_snd, CycleQ2LiteralAbelJacobiTimeProjection.q_original]

variable (hV : seedBasePoint ∈ V)

def relativeTangent : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ Time i V :=
  tangentLift V hV ≫ fixedToTime i V b hb

theorem tangent_to_incidence :
    relativeTangent i V b hb hV ≫ pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι =
      firstOrderParameterPoint := by
  simp only [relativeTangent, Category.assoc, fixedToTime_snd_assoc, morphismRestrict_ι,
    tangentLift_fac_assoc, timeTangent_to_incidence]

theorem tangent_seed :
    firstOrderClosedPoint ≫ relativeTangent i V b hb hV = seedLift V hV ≫ fixedToTime i V b hb := by
  rw [relativeTangent, ← Category.assoc, tangentLift_at_seed]

theorem tangent_over_coefficients :
    relativeTangent i V b hb hV ≫ timeMap i V = structureDual ≫ b := by
  simp only [relativeTangent, Category.assoc, fixedToTime_fst, tangentLift_fac_assoc]
  exact (pullback.lift_fst_assoc ..)

private theorem tangentFamily_square :
    IsPullback (pullback.fst (tangentLift V hV) (projection V t))
      (pullback.snd _ _ ≫ fixedToSurface i V t b hb) (relativeTangent i V b hb hV) (curveMap i V t) :=
  (IsPullback.of_hasPullback (tangentLift V hV) (projection V t)).paste_vert
    (fixed_curve_square i V t b hb)

/-- The fibre along the relative tangent is the original embedded first-order curve. -/
def tangentFamilyIso :
    firstOrderCurve t ≅ pullback (relativeTangent i V b hb hV) (curveMap i V t) :=
  firstOrderIso V t hV ≪≫ (tangentFamily_square i V t b hb hV).isoPullback

theorem tangentFamily_q :
    (tangentFamilyIso i V t b hb hV).hom ≫ pullback.snd _ _ ≫ relativeQ i V t =
      (CycleQ2LiteralIncidenceTimeFamily.firstOrderIso t).hom ≫ pullback.snd _ _ ≫
        toFixedThreefold t ≫ fixedToAmbient i b hb := by
  have h := congrArg (fun f => (firstOrderIso V t hV).hom ≫ f ≫ relativeQ i V t)
    (tangentFamily_square i V t b hb hV).isoPullback_hom_snd
  simpa only [tangentFamilyIso, Iso.trans_hom, Category.assoc, fixed_q,
    CycleQ2LiteralAbelJacobiTimeProjection.firstOrder_to_q_assoc] using h

theorem tangent_nonconstant :
    relativeTangent i V b hb hV ≠ structureDual ≫ seedLift V hV ≫ fixedToTime i V b hb := by
  intro h
  have he := congrArg (fun f => f ≫ pullback.snd i (V.ι ≫ parameterToSextics) ≫ V.ι) h
  rw [tangent_to_incidence] at he
  simp only [Category.assoc, fixedToTime_snd_assoc, morphismRestrict_ι, seedLift_fac_assoc,
    seed_to_incidence] at he
  apply timeTangent_nonconstant
  apply pullback.hom_ext
  · simp only [timeTangent, seed, Category.assoc, pullback.lift_fst, Category.comp_id]
  · simpa only [timeTangent, seed, Category.assoc, pullback.lift_snd] using he

end CycleQ2LiteralIncidenceRelativeCylinder
end

#print axioms CycleQ2LiteralIncidenceRelativeCylinder.fixed_surface_square
#print axioms CycleQ2LiteralIncidenceRelativeCylinder.tangentFamily_q
#print axioms CycleQ2LiteralIncidenceRelativeCylinder.fixed_q
#print axioms CycleQ2LiteralIncidenceRelativeCylinder.tangent_nonconstant
