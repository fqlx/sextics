import Proposal.GeometricLiteralMovingResidueFaces
import Proposal.GeometricSeedSectionCurveRows
import Proposal.GeometricSurfaceOverlap

/-!
# Differentials of the actual row as coordinates on its Jacobian patches

Augment the original two surface equations by the actual section row and a
fourth polynomial. Its localization carries the original Cartier equation
to the literal section of its dehomogenized row on every subopen.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingResidueCoordinates
open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricAffineChartSections CycleQ2GeometricPrincipalChartSections
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralMovingResidueFaces
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionCurveRows CycleQ2RelativeConstantSection

abbrev chartEquations (i : Fin 3) := dehomogenizedEquations 57 1 i.succ
abbrev rowPolynomial (t : Fin 3 → ℂ) (i a : Fin 3) :=
  dehomogenize i.succ (relativeSectionPolynomial seed t a)

variable (t : Fin 3 → ℂ) (i a : Fin 3) (s : SurfacePoly)

abbrev rowJacobian := augmentedJacobian (chartEquations i) (rowPolynomial t i a) s
abbrev rowOpen := principalOpen (coordinateAffineChart 57 1 i.succ) (rowJacobian t i a s)
abbrev rowChart := principalChart (coordinateAffineChart 57 1 i.succ) (rowJacobian t i a s)
theorem rowChart_complex :
    (rowChart t i a s).inv ≫ (rowOpen t i a s).ι ≫ CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away (rowJacobian t i a s)))) :=
  principalChart_overComplex _ _ _ (coordinateAffineChart_overComplex 57 1 i.succ)

variable {W : Surface.Opens} (j : FrameData W)
variable (h : W ≤ rowOpen t j.chart j.pivot.1 s)

abbrev rowSubopen := Over.mk (homOfLE h)
abbrev surfaceEquations := chartEquations j.chart
abbrev framePolynomial := rowPolynomial t j.chart j.pivot.1

/-- The actual moving equation is the section of its dehomogenized polynomial
in the augmented-Jacobian chart. -/
theorem rowSection :
    chartSection (rowChart t j.chart j.pivot.1 s) (rowSubopen t s j h)
      (algebraMap SurfacePoly (AdjunctionPatch (surfaceEquations j) (framePolynomial t j) s) (framePolynomial t j)) = frameEquation t j := by
  let R := SurfaceChartRing (surfaceEquations j)
  let A := AdjunctionPatch (surfaceEquations j) (framePolynomial t j) s
  rw [IsScalarTower.algebraMap_apply SurfacePoly R A, principal_chartSection]
  exact (sectionRows_polynomial t j.chart W j.within j.pivot.1).symm

end CycleQ2LiteralMovingResidueCoordinates
end

#print axioms CycleQ2LiteralMovingResidueCoordinates.rowSection
