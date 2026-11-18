import Proposal.GeometricLiteralMovingResidueCoordinates
import Proposal.GeometricJacobianCotangentPatch

/-!
# The moving equation as a surface cotangent basis vector

On each augmented row chart the differential of the actual section row is
the first cotangent basis vector and the exterior square of sections gives
every canonical two-form, including on nonaffine subopens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingResidueCoordinates
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricAffineChartSections CycleQ2GeometricPrincipalChartSections
  CycleQ2GeometricFunctionalDifferentials CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricExteriorLocalFrames
  CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricDifferentialSheaf
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralMovingResidueFaces
  CycleQ2SeedSectionDivisorTransitions
  CycleQ2SeedSectionCurveRows CycleQ2RelativeConstantSection

variable (t : Fin 3 → ℂ) (s : SurfacePoly) {W : Surface.Opens} (j : FrameData W)
variable (h : W ≤ rowOpen t j.chart j.pivot.1 s)

/-- The first cotangent basis vector on every subopen is de for the original
moving Cartier generator, even when that subopen is nonaffine. -/
def rowBasis : Basis (Fin 2) Γ(Surface,W) (OneForms W) :=
  chartSectionBasis (rowChart t j.chart j.pivot.1 s) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1)
    (rowChart_complex t j.chart j.pivot.1 s)
    (localSurfaceKaehlerBasis (surfaceEquations j) (framePolynomial t j) s) (rowSubopen t s j h)


theorem rowBasis_zero : rowBasis t s j h 0 = equationDifferential W (frameEquation t j) :=
  (CycleQ2JacobianCotangentPatch.firstBasis_D _ _ _ _ _ (rowChart_complex t j.chart j.pivot.1 s) (rowSubopen t s j h)).trans
    (congrArg (equationDifferential W) (rowSection t s j h))

include h in
/-- Sheafification of the exterior square is an isomorphism on sections of
each of these opens. -/
theorem exteriorSection_bijective :
    Function.Bijective (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W) :=
  CycleQ2JacobianCotangentPatch.exterior_bijective _ _ _ _ _ (rowChart_complex t j.chart j.pivot.1 s) h

end CycleQ2LiteralMovingResidueCoordinates
end

#print axioms CycleQ2LiteralMovingResidueCoordinates.rowBasis_zero
#print axioms CycleQ2LiteralMovingResidueCoordinates.exteriorSection_bijective
