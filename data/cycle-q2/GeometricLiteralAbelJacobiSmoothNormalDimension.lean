import Proposal.GeometricLiteralAbelJacobiSmoothNormal
import Proposal.GeometricLiteralAbelJacobiSeedLiftDimension

/-!
# Relative dimension of the smooth curve carrying the nonzero normal

The smooth incidence neighborhood has relative dimension one, and the
infinitesimal deformation of the same section retains that relative
dimension under base change to the dual numbers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSmoothNormalDimension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2IncidenceFirstOrder
  CycleQ2FirstOrderCurve CycleQ2FirstOrderNeighborhood CycleQ2RelativeConstantCurve

theorem firstOrderCurve_dimension_of_neighborhood (t : Fin 3 → ℂ) (V : parameterScheme.Opens)
    (hseed : seedBasePoint ∈ V)
    (hs : SmoothOfRelativeDimension 1 ((relativeCurveToBase incidencePoint t) ∣_ V)) :
    SmoothOfRelativeDimension 1 (firstOrderCurveToBase t) := by
  let f := relativeCurveToBase incidencePoint t
  let j := IsOpenImmersion.lift V.ι firstOrderParameterPoint (by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨firstOrderParameterPoint z, (firstOrderParameterPoint_apply z).symm ▸ hseed⟩, rfl⟩)
  have hj : j ≫ V.ι = firstOrderParameterPoint := IsOpenImmersion.lift_fac _ _ _
  have hsq := (IsPullback.of_hasPullback (f ∣_ V) j).paste_horiz (isPullback_morphismRestrict f V).flip
  rw [hj] at hsq
  let e := (firstOrderCurve_isPullback t).isoIsPullback _ _ hsq
  rw [← (firstOrderCurve_isPullback t).isoIsPullback_hom_snd _ _ hsq]
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    e.hom (pullback.snd (f ∣_ V) j)).mpr
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ hs

open CycleQ2FirstOrderChartReduction CycleQ2SpecializedProjectiveCurve CycleQ2SeedConeSection
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiRelativeNormal CycleQ2LiteralAbelJacobiSeedLift
  CycleQ2LiteralAbelJacobiSmoothNormal CycleQ2LiteralAbelJacobiSeedLiftDimension

attribute [local instance] CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra

/-- The same vector that gives a nonzero cubic normal moves in a proper
family of nonempty smooth curves of relative dimension one, including
its original dual-number germ. -/
theorem exists_dimension_one_moving_curve_nonzero_normal :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧ t ≠ 0 ∧
      ∃ hf : ∀ i : Fin 4, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
        SmoothOfRelativeDimension 1 (specializedCurveToBase seed t) ∧
        Nonempty (specializedCurve seed t) ∧
        SmoothOfRelativeDimension 1 (firstOrderCurveToBase t) ∧
        Flat (firstOrderCurveToBase t) ∧ IsProper (firstOrderCurveToBase t) ∧
        (∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
          SmoothOfRelativeDimension 1 ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
          IsProper ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
          Function.Surjective ((relativeCurveToBase incidencePoint t) ∣_ V)) ∧
        ∃ j : Fin 3, @relativeNormal t j.succ (hf j.succ)
          ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 ∧
          ∃ v : Derivation ℂ (T j.succ) (A t j.succ),
            (∀ x : idealOnT t j.succ, v x.val =
              @relativeNormal t j.succ (hf j.succ) ((idealOnT t j.succ).toCotangent x)) ∧
            v (cubicOnT j.succ) ≠ 0 := by
  obtain ⟨t, ht, hne, hf, _, hflat, hproper, hnonempty, _, _, hnormal⟩ :=
    exists_smooth_moving_curve_nonzero_normal
  have h : SeedMinorCover t := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  obtain ⟨V, hV, hdim, hp, hsurj⟩ := dimension_one_neighborhood_of_seedMinorCover t h
  exact ⟨t, ht, hne, hf, smooth_seed_of_seedMinorCover t h, hnonempty,
    firstOrderCurve_dimension_of_neighborhood t V hV hdim, hflat, hproper,
    ⟨V, hV, hdim, hp, hsurj⟩, hnormal⟩

end CycleQ2LiteralAbelJacobiSmoothNormalDimension

end

#print axioms CycleQ2LiteralAbelJacobiSmoothNormalDimension.exists_dimension_one_moving_curve_nonzero_normal
