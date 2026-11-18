import Proposal.GeometricNormalSheafComparison
import Proposal.GeometricLiteralOrbitChern

/-!
# The normal line of each translated incidence curve

The translated closed immersion differs by an actual automorphism of
the target surface. The Cartesian restriction comparison for normal
sheaves therefore transports its intrinsic normal to the same degree
minus two line on the original source curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralOrbitCurveNormal
open CategoryTheory AlgebraicGeometry CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
  CycleQ2SourceNormalSheaf CycleQ2SourceNormalRestriction
  CycleQ2LiteralOrbitChern CycleQ2LiteralOrbitAction

private def normalTargetIso {X Y Z : Scheme.{0}} (j : X ⟶ Y) (e : Y ≅ Z) :
    sourceNormal (j ≫ e.hom) ≅ sourceNormal j := by
  have h : IsPullback (j ≫ e.hom) (𝟙 X) e.inv j :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  exact (sourceNormalRestrictionIso j (j ≫ e.hom) (𝟙 X) e.inv h).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback (𝟙 X)).app (sourceNormal j) ≪≫
    (Scheme.Modules.pullbackId X).app (sourceNormal j)

/-- The genuine intrinsic normal sheaf of the translated inclusion,
in the two original quartic frames on C. -/
def componentNormalModel (z : ℂ) (hz : z ^ 3 = 1) :
    sourceNormal (CycleQ2GeometricLiteralSurface.curveToSurface 57 1 ≫
      (closedProjectiveAction z hz).inv) ≅ normalModuleSheaf 57 1 :=
  normalTargetIso _ (closedProjectiveAction z hz).symm ≪≫ CycleQ2IntrinsicNormalModel.intrinsicNormalIso

end CycleQ2LiteralOrbitCurveNormal
end

#print axioms CycleQ2LiteralOrbitCurveNormal.componentNormalModel
