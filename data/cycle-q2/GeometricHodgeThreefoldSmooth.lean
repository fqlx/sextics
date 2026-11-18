import Proposal.GeometricHodgeThreefoldProper
import Proposal.GeometricHodgeThreefoldGradient
import Proposal.GeometricHodgeEulerChartBinding
import Proposal.GeometricHodgeEulerContractionCharts
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth relative dimension of the original weighted projective family

The four affine derivatives generate the unit ideal on each degree-one
chart. Localizing at any one derivative gives a standard smooth presentation
of relative dimension three. The native chart isomorphisms carry these
covers to the original projective structure morphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefold

open CategoryTheory AlgebraicGeometry MvPolynomial CycleQ2GenericSexticGradient
open CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding CycleQ2HodgeEulerContractionCharts

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

theorem coordinateOpen_smoothDimension (hg : IsUnit (φ gradientOpen)) (i : Fin 4) :
    SmoothOfRelativeDimension 3 ((coordinateOpen φ i).ι ≫ toBase φ) := by
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 3)
    (affineChart φ i).inv ((coordinateOpen φ i).ι ≫ toBase φ)).mp
  rw [affineChart_overBase]
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 3)).mpr
  refine ⟨_, chartGradient_span φ hg i, ?_⟩
  rintro _ ⟨j, rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension 3
    ((algebraMap (chart φ i) (Patch (F φ i) j)).comp (algebraMap R (chart φ i)))
  rw [← IsScalarTower.algebraMap_eq R (chart φ i) (Patch (F φ i) j)]
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 3).mpr (patch_standardSmooth _ _)

theorem toBase_smoothDimension (h : IsUnit (φ goodParameter)) :
    SmoothOfRelativeDimension 3 (toBase φ) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 3)
    (fun i : Fin 4 => coordinateOpen φ i) (coordinateOpens_cover_of_good φ h)
  rw [goodParameter, map_mul, IsUnit.mul_iff] at h
  exact coordinateOpen_smoothDimension φ h.1

theorem fermat_smoothDimension : SmoothOfRelativeDimension 3 (toBase seedEvaluation) :=
  toBase_smoothDimension seedEvaluation (by rw [goodParameter_seed]; exact isUnit_one)

/-- The coefficient ring of the common principal open, including the Fermat point. -/
abbrev GoodBase := Localization.Away goodParameter

def goodFamily := toBase (algebraMap CoeffRing GoodBase)

theorem goodFamily_proper : IsProper goodFamily :=
  toBase_proper (algebraMap CoeffRing GoodBase)

theorem goodFamily_smoothDimension : SmoothOfRelativeDimension 3 goodFamily :=
  toBase_smoothDimension _ (IsLocalization.Away.algebraMap_isUnit goodParameter)

def fermatOnGoodBase : GoodBase →+* ℂ :=
  IsLocalization.Away.lift goodParameter (g := seedEvaluation) (by
    rw [goodParameter_seed]
    exact isUnit_one)

@[simp] theorem fermatOnGoodBase_apply (c : CoeffRing) :
    fermatOnGoodBase (algebraMap CoeffRing GoodBase c) = seedEvaluation c :=
  IsLocalization.Away.lift_eq _ _ c

end CycleQ2GeometricHodgeThreefold
end

#print axioms CycleQ2GeometricHodgeThreefold.toBase_smoothDimension
#print axioms CycleQ2GeometricHodgeThreefold.goodFamily_smoothDimension
