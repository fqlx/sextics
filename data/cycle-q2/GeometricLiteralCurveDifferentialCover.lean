import Proposal.GeometricLiteralThreefoldMovingVolume
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Detecting curve differentials on the actual surface Jacobian cover

The sixteen ordered pairs of chart coordinates give a unit ideal on the
surface. Its image is the unit ideal on the section curve, so two genuine
one-forms agree if their restrictions to these Jacobian opens agree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCurveDifferentialCover

open MvPolynomial CycleQ2GeometricSurfaceAdjunction CycleQ2FullSurfaceJacobianCover
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralThreefoldMovingVolume CycleQ2LiteralThreefoldSurfaceNormal

section Localization

variable {A : Type} [CommRing A] [Algebra ℂ A]

theorem form_ext_of_span {ι : Type} (a : ι → A) (ha : Ideal.span (Set.range a) = ⊤)
    {α β : KaehlerDifferential ℂ A} (h : ∀ i, KaehlerDifferential.map ℂ ℂ A (Localization.Away (a i)) α =
      KaehlerDifferential.map ℂ ℂ A (Localization.Away (a i)) β) : α = β := by
  apply sub_eq_zero.mp
  apply Module.eq_zero_of_isLocalized_span (Set.range a) ha
    (fun r => KaehlerDifferential ℂ (Localization.Away r.val))
    (fun r => KaehlerDifferential.map ℂ ℂ A (Localization.Away r.val))
  rintro ⟨r, i, rfl⟩
  rw [map_sub, h, sub_self]

end Localization

attribute [local instance] CycleQ2LiteralAbelJacobiContraction.seedChartCommRing

variable (t : Fin 3 → ℂ) (j : Fin 3)
private abbrev coordinate (a : Fin 4) : P := X (variableIndex a)
private abbrev element (p : Fin 4 × Fin 4) : A t j.succ :=
  surfaceToCurve t j.succ (augmentedJacobian (E j.succ) (coordinate p.1) (coordinate p.2))

theorem curve_jacobians_span : Ideal.span (Set.range (element t j)) = ⊤ := by
  have h := congrArg (Ideal.map (surfaceToCurve t j.succ).toRingHom) (augmentedCoordinateIdeal_eq_top j)
  rw [augmentedCoordinateIdeal, Ideal.map_span, ← Set.range_comp, Ideal.map_top] at h
  refine Eq.trans (congrArg (fun b : Fin 4 × Fin 4 → A t j.succ => Ideal.span (Set.range b)) ?_) h
  funext p
  rfl

/-- The localization maps of the original affine seed curve jointly detect its
one-forms. The particular list of Jacobian opens is an actual proved cover. -/
theorem native_curve_form_ext {α β : KaehlerDifferential ℂ (A t j.succ)} (h : ∀ (p : Fin 4 × Fin 4),
    KaehlerDifferential.map ℂ ℂ (A t j.succ) (CurvePatch t j.succ (coordinate p.1) (coordinate p.2)) α =
      KaehlerDifferential.map ℂ ℂ (A t j.succ) (CurvePatch t j.succ (coordinate p.1) (coordinate p.2)) β) :
    α = β := form_ext_of_span (element t j) (curve_jacobians_span t j) h

end CycleQ2LiteralCurveDifferentialCover
end

#print axioms CycleQ2LiteralCurveDifferentialCover.native_curve_form_ext
