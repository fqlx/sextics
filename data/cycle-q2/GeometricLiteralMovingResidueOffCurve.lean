import Proposal.GeometricLiteralMovingResidueAffineCurve
import Proposal.GeometricLiteralMovingResidueAffineNumerators

/-!
# Vanishing of the moving residue away from the curve

If a framed affine open misses the curve, its curve section ring is the
zero ring. The moving equation then generates the unit ideal, so its
canonical numerator quotient and all residue sections vanish.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingResidueOffCurve

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle (Surface)
open CycleQ2SeedSectionDivisorTransitions (FrameData)
open CycleQ2SeedSectionAffineInjective (ChartRegular)
open CycleQ2SeedSectionSheafCurveBinding (curveToSurface)
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open CycleQ2LiteralMovingResidueFaces (frameEquation)
open CycleQ2LiteralMovingResidueExact (residueQuotient)
open CycleQ2LiteralMovingResidueAdjunction
open CycleQ2LiteralMovingResidueAdjunction.AffineFrame
open CycleQ2LiteralMovingResidueAffineNumerators (numeratorToResidue_surjective)

attribute [local instance] AffineFrame.curveAlgebra
local instance canonicalSectionModule (W : Surface.Opens) :
    Module Γ(Surface,W) (CanonicalForms.val.obj (op W)) := (CanonicalForms.val.obj (op W)).isModule

variable {W : Surface.Opens} (hW : IsAffineOpen W) (t : Fin 3 → ℂ)
  (ht : ∀ i, ChartRegular t i) (j : FrameData W) (hdisj : (curveToSurface t) ⁻¹ᵁ W = ⊥)

include hdisj in
private theorem curveRing_subsingleton : Subsingleton (CurveRing t W) := by
  change Subsingleton Γ(Curve t, (curveToSurface t) ⁻¹ᵁ W)
  rw [hdisj]
  infer_instance

include hW ht j hdisj in
/-- On a framed affine open disjoint from the curve the residue quotient
has only the zero section. -/
theorem residueQuotient_subsingleton :
    Subsingleton ((residueQuotient t).obj.obj (op W)) := by
  let := curveRing_subsingleton t hdisj
  have he : (Ideal.span {frameEquation t j} : Ideal Γ(Surface,W)) = ⊤ :=
    (curveKer_eq_span t ht j).symm.trans (RingHom.ker_eq_top_of_subsingleton _)
  let : Subsingleton (Numerators (M := CanonicalForms.val.obj (op W)) (frameEquation t j)) := by
    apply Submodule.Quotient.subsingleton_iff.mpr
    change (Ideal.span {frameEquation t j} : Ideal Γ(Surface,W)) •
      (⊤ : Submodule Γ(Surface,W) (CanonicalForms.val.obj (op W))) = ⊤
    rw [he, Submodule.top_smul]
  exact (numeratorToResidue_surjective t ht j hW).subsingleton

include hdisj in
/-- The native curve differential comparison is bijective away from the
curve, where both groups of sections vanish. -/
theorem curveAdjunction_bijective_of_disjoint :
    Function.Bijective (curveAdjunction hW t ht j) := by
  let := curveRing_subsingleton t hdisj
  let := Module.subsingleton (CurveRing t W) (KaehlerDifferential ℂ (CurveRing t W))
  let := residueQuotient_subsingleton hW t ht j hdisj
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end CycleQ2LiteralMovingResidueOffCurve
end

#print axioms CycleQ2LiteralMovingResidueOffCurve.curveAdjunction_bijective_of_disjoint
