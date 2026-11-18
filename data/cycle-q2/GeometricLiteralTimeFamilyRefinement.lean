import Proposal.GeometricLiteralAbelJacobiTimeProjection
import Proposal.GeometricLiteralAmbientCylinder

/-!
# Restricting the moving family to a prescribed parameter-curve open

Every smaller open of the fixed-sextic time curve comes from a smaller
incidence-parameter open. The moving family restricts by an actual
pullback, preserving its projection into the fixed threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeFamilyRefinement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2LiteralAbelJacobiTimeProjection CycleQ2LiteralAmbientCylinder
  CycleQ2IncidenceTimeCurve CycleQ2IncidenceFirstOrder CycleQ2IncidenceEtaleParameter
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

private instance : IsClosedImmersion seedSextic := by
  have h : Spec.map (CommRingCat.ofHom sexticEval) = seedSextic := by
    rw [seedSextic, seedPointMorphism, parameterToSextics, ← Spec.map_comp]
    rfl
  rw [← h]
  apply IsClosedImmersion.spec_of_surjective
  intro c
  refine ⟨C c, ?_⟩
  change seedMap (sexticToParameter (C c)) = c
  rw [CycleQ2GenericTimeDerivation.sexticToParameter_C, CycleQ2IncidenceSeedFiber.seedMap_complex]

private instance : IsClosedImmersion toIncidence := by unfold toIncidence; infer_instance

/-- Choose the smaller incidence neighborhood inducing a prescribed time open. -/
theorem exists_parameter_refinement (V : parameterScheme.Opens) (U : Curve.Opens)
    (hle : U ≤ timeOpen V) : ∃ W ≤ V, timeOpen W = U := by
  obtain ⟨T, hT, e⟩ := toIncidence.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
  let W : parameterScheme.Opens := ⟨T,hT⟩
  have hw : timeOpen W = U := TopologicalSpace.Opens.ext e
  refine ⟨V ⊓ W, inf_le_left, ?_⟩
  change toIncidence ⁻¹ᵁ (V ⊓ W) = U
  rw [Scheme.Hom.preimage_inf, show toIncidence ⁻¹ᵁ W = U from hw, inf_eq_right.mpr hle]

variable {W V : parameterScheme.Opens} (h : W ≤ V) (t : Fin 3 → ℂ)

abbrev timeMap := Curve.homOfLE (toIncidence.preimage_mono h)

def familyMap : family W t ⟶ family V t :=
  (family_square V t).lift (projection W t ≫ timeMap h) (familyToFull W t) (by simp [timeMap])

@[reassoc (attr := simp)] theorem familyMap_base :
    familyMap h t ≫ projection V t = projection W t ≫ timeMap h :=
  (family_square V t).lift_fst ..

@[reassoc (attr := simp)] theorem familyMap_toFull :
    familyMap h t ≫ familyToFull V t = familyToFull W t :=
  (family_square V t).lift_snd ..

@[reassoc (attr := simp)] theorem familyMap_toFixed :
    familyMap h t ≫ q V t = q W t := by rw [q, familyMap_toFull_assoc]; rfl

theorem family_pullback : IsPullback (projection W t) (familyMap h t) (timeMap h) (projection V t) := by
  have H : IsPullback (projection W t) (familyMap h t ≫ familyToFull V t)
      (timeMap h ≫ (timeOpen V).ι) (CycleQ2LiteralIncidenceTimeFamily.toCurve t) := by
    simpa only [familyMap_toFull, timeMap, Scheme.homOfLE_ι] using family_square W t
  exact H.of_bot (familyMap_base h t).symm (family_square V t)

include h in
/-- The smooth, proper, surjective curve family stays so on each smaller
time open in the incidence project. -/
theorem restrict_properties (hs : SmoothOfRelativeDimension 1 (projection V t))
    (hp : IsProper (projection V t)) (hc : Function.Surjective (projection V t)) :
    SmoothOfRelativeDimension 1 (projection W t) ∧ IsProper (projection W t) ∧
      Function.Surjective (projection W t) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let : Surjective (projection V t) := ⟨hc⟩
  let : Surjective (projection W t) := MorphismProperty.of_isPullback (family_pullback h t).flip inferInstance
  exact ⟨MorphismProperty.of_isPullback (family_pullback h t).flip hs,
    MorphismProperty.of_isPullback (family_pullback h t).flip hp, (projection W t).surjective⟩

end CycleQ2LiteralTimeFamilyRefinement
end

#print axioms CycleQ2LiteralTimeFamilyRefinement.exists_parameter_refinement
#print axioms CycleQ2LiteralTimeFamilyRefinement.family_pullback
#print axioms CycleQ2LiteralTimeFamilyRefinement.restrict_properties
