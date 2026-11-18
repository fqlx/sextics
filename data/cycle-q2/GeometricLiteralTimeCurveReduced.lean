import Proposal.GeometricLiteralTimeCurveCompletion
import Proposal.GeometricLiteralAbelJacobiSeedLiftRegular

/-!
# Reducedness of the proper parameter base

The original fixed-sextic time curve is smooth over the complex field. The
coordinate rings of affine patches of its projective closure embed into
sections on that reduced dense open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCurveReduced

open CategoryTheory AlgebraicGeometry CycleQ2LiteralIncidenceTimeCurve
  CycleQ2LiteralTimeCurveAffineEmbedding CycleQ2LiteralTimeCurveCompletion

instance curve_reduced : AlgebraicGeometry.IsReduced Curve := by
  have hcomp : Curve.toSpecΓ ≫ Spec.map coefficients = toComplex := by
    rw [coefficients, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have h : SmoothOfRelativeDimension 1 (Spec.map coefficients) := by
    apply (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
      Curve.toSpecΓ (Spec.map coefficients)).mp
    rw [hcomp]
    exact smooth_parameter_curve
  let : _root_.IsReduced CoordinateRing :=
    CycleQ2LiteralAbelJacobiSeedLiftRegular.reduced_of_smoothDimension 1 coefficients.hom
      ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp h)
  exact isReduced_of_isAffine_isReduced (X := Curve)

private theorem reduced_image {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    [AlgebraicGeometry.IsReduced X] : AlgebraicGeometry.IsReduced f.image := by
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover (X := f.image) f.ker.subschemeCover.openCover).mpr
  change ∀ U : Y.affineOpens, AlgebraicGeometry.IsReduced
    (Spec (CommRingCat.of (Γ(Y, U.1) ⧸ f.ker.ideal U)))
  intro U
  apply (affine_isReduced_iff _).mpr
  let : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U.1) :=
    isReduced_of_injective (f.toImage.app _).hom (f.toImage_app_injective U)
  exact isReduced_of_injective (f.ker.subschemeObjIso U).inv.hom
    (f.ker.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.injective

/-- The actual projective closure of any open in the smooth time curve is reduced. -/
instance completion_reduced (U : Curve.Opens) : AlgebraicGeometry.IsReduced (Completion U) :=
  reduced_image (intoProjective U)

end CycleQ2LiteralTimeCurveReduced

#print axioms CycleQ2LiteralTimeCurveReduced.curve_reduced
#print axioms CycleQ2LiteralTimeCurveReduced.completion_reduced
