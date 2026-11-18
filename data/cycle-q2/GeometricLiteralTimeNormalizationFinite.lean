import Proposal.GeometricLiteralTimeCurveNormalization
import Proposal.GeometricLiteralTimeCurveReduced
import Proposal.GeometricFiniteTypeNormalization
import Proposal.GeometricReducedNormalizationFinite
import Proposal.GeometricDenseOpenTotalFractions
import Proposal.GeometricDenseOpenAffineSections

/-!
# Finiteness of the normalized proper time base

On an affine chart of the projective completion the original dense open
has a section algebra contained in the total fraction ring. The closure
of the chart ring inside those sections is finite because the chart is a
reduced algebra of finite type over the complex numbers. These affine
calculations give a finite normalization and a proper base over the
complex field that still contains the original smooth time open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeNormalizationFinite

open AlgebraicGeometry CategoryTheory CycleQ2LiteralIncidenceTimeCurve
  CycleQ2LiteralTimeCurveCompletion CycleQ2LiteralTimeCurveNormalization

variable (U : Curve.Opens)

instance finite : IsFinite (toCompletion U) := by
  let j := inclusion U
  change IsFinite j.fromNormalization
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro V hV
  let A := Γ(Completion U, V)
  let B := Γ(U.toScheme, j ⁻¹ᵁ V)
  let p := structureMap U
  let hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  let c := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ p.appLE ⊤ V hle
  let : Algebra ℂ A := c.hom.toAlgebra
  let : Algebra.FiniteType ℂ A :=
    (p.finiteType_appLE (isAffineOpen_top _) hV hle).comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  let : Algebra A B := (j.app V).hom.toAlgebra
  obtain ⟨φ, hφ⟩ := CycleQ2DenseOpenTotalFractions.sections_embedding A
    (CycleQ2DenseOpenAffineSections.chartOpen j hV) (CycleQ2DenseOpenAffineSections.dense j hV)
  let e := CycleQ2DenseOpenAffineSections.sectionEquiv j hV
  let : Module.Finite A (integralClosure A B) :=
    CycleQ2ReducedNormalizationFinite.finiteType_integralClosure_of_fraction_embedding ℂ
      CycleQ2FiniteTypeNormalization.domainNormalizationFinite A (φ.comp e.toAlgHom)
        (hφ.comp e.injective)
  rw [j.fromNormalization_app hV, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (j.normalizationObjIso hV).symm.commRingCatIsoToRingEquiv.surjective).comp
      (RingHom.finite_algebraMap.mpr inferInstance)

/-- The normalization preserving the original smooth open is proper over ℂ. -/
instance proper : IsProper (toComplexPoint U) := by
  unfold toComplexPoint
  infer_instance

/-- The proper normalized base recovers the smooth one-dimensional parameter
open as its full scheme-theoretic inverse image. -/
theorem normalized_base :
    IsProper (toComplexPoint U) ∧ IsFinite (toCompletion U) ∧
    IsIso (CategoryTheory.Limits.pullback.snd (toCompletion U) (inclusion U)) ∧
    SmoothOfRelativeDimension 1 (openInclusion U ≫ toComplexPoint U) :=
  ⟨inferInstance, inferInstance, toCompletion_over_open_isIso U, smooth_on_original_open U⟩

end CycleQ2LiteralTimeNormalizationFinite
#print axioms CycleQ2LiteralTimeNormalizationFinite.finite
#print axioms CycleQ2LiteralTimeNormalizationFinite.normalized_base
