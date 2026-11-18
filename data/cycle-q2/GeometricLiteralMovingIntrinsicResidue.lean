import Proposal.GeometricClosedEmbeddingSheafDescent
import Proposal.GeometricLiteralMovingCurveDifferential
import Proposal.GeometricLiteralMovingCurveTrace
import Proposal.GeometricLiteralMovingResidueSmooth

/-!
# Adjunction on the moving curve

The conormal wedge descends to a morphism on the curve from its own
Kähler differentials to the inverse image of the pole quotient. The
trace of that morphism is the differential trace obtained on the
ambient surface. An isomorphism of the wedge on the surface descends
to an isomorphism on the curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingIntrinsicResidue
open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2ClosedEmbeddingSheafExact CycleQ2ClosedEmbeddingSheafDescent
  CycleQ2ClosedEmbeddingCohomology CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafCurveBinding CycleQ2LiteralMovingResidueCurve
  CycleQ2LiteralMovingCurveTrace CycleQ2LiteralMovingCurveDifferentialNonzero

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- The wedge-residue morphism between sheaves on the curve itself. -/
def curveAdjunction : curveForms t ⟶ curveResidues t :=
  unpushHom (curveToSurface t).base (curveToSurface t).isClosedEmbedding
    (curveResidue t ht ≫ (quotientPushIso t).hom)

theorem push_curveAdjunction :
    (push (curveToSurface t).base).map (curveAdjunction t ht) =
      curveResidue t ht ≫ (quotientPushIso t).hom := push_unpushHom _ _ _

/-- An invertible wedge on the surface is invertible on the curve. -/
def curveAdjunctionIso [IsIso (curveResidue t ht)] : curveForms t ≅ curveResidues t :=
  unpushIso (curveToSurface t).base (curveToSurface t).isClosedEmbedding
    (asIso (curveResidue t ht) ≪≫ quotientPushIso t)

theorem curveAdjunctionIso_hom [IsIso (curveResidue t ht)] :
    (curveAdjunctionIso t ht).hom = curveAdjunction t ht := unpushIso_hom _ _ _

/-- On the retained algebraically independent family, the actual one-form
sheaf of the curve is isomorphic to the restricted canonical pole quotient. -/
def independentCurveAdjunction (hi : AlgebraicIndependent ℚ t) : curveForms t ≅ curveResidues t := by
  letI := CycleQ2LiteralMovingResidueSmooth.curveResidue_isIso_of_independent t ht hi
  exact curveAdjunctionIso t ht

theorem independentCurveAdjunction_hom (hi : AlgebraicIndependent ℚ t) :
    (independentCurveAdjunction t ht hi).hom = curveAdjunction t ht := by
  letI := CycleQ2LiteralMovingResidueSmooth.curveResidue_isIso_of_independent t ht hi
  exact curveAdjunctionIso_hom t ht

/-- The cohomological trace of the intrinsic adjunction map agrees on every
class with the algebraic trace computed by the pole sequence on the surface. -/
theorem curveAdjunction_trace (x : (curveForms t).H' 1 ⊤) :
    curveResidueTrace t ht (x.comp (Ext.mk₀ (curveAdjunction t ht)) (add_zero 1)) =
      differentialTrace t ht x := by
  change CycleQ2LiteralMovingQuotientTrace.residueTrace t ht
    (((pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding
        (curveResidues t) 1) (x.comp (Ext.mk₀ (curveAdjunction t ht)) (add_zero 1))).comp
      (Ext.mk₀ (quotientPushIso t).inv) (add_zero 1)) = _
  rw [pushHEquiv_natural, push_curveAdjunction, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

end CycleQ2LiteralMovingIntrinsicResidue
end

#print axioms CycleQ2LiteralMovingIntrinsicResidue.curveAdjunction_trace
