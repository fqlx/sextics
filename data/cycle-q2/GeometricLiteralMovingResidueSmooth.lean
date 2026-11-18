import Proposal.GeometricLiteralMovingResidueCurveIso
import Proposal.GeometricLiteralMovingResidueRowBasis
import Proposal.GeometricLiteralMovingResidueSmoothChart
import Proposal.GeometricLiteralMovingResidueCoordinateBasis
import Proposal.GeometricLiteralMovingResidueOffCurve
import Proposal.GeometricLiteralResidueRowCover
import Proposal.GeometricLiteralAbelJacobiChartRegular

/-!
# Smooth moving adjunction on the given Cartier curve

The ordinary one-forms of a smooth moving member identify with its simple-pole
quotient. The local equations, native closed immersion and gluing morphism
are the same ones used for the residue boundary.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingResidueSmooth

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricAffineOverlap CycleQ2LiteralMovingResidueBasis
  CycleQ2LiteralMovingResidueCurve CycleQ2LiteralMovingResidueCurveIso
  CycleQ2LiteralMovingResidueAdjunction CycleQ2LiteralMovingResidueAffineNumerators
  CycleQ2LiteralMovingResidueCoordinateBasis CycleQ2LiteralMovingResidueCoordinates
  CycleQ2SeedSectionAffineInjective

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- The actual adjunction morphism is invertible on the entire surface if
the active row Jacobian opens cover the given curve. -/
theorem curveResidue_isIso (hc : RowCover t) : IsIso (curveResidue t ht) := by
  apply curveResidue_isIso_of_basis t ht (fun W : {W : FramedAffine // Adapted t W} => W.val)
    (isBasis_adapted t hc)
  rintro ⟨W,hW⟩
  rcases hW with hdisj | ⟨s,hs⟩
  · exact CycleQ2LiteralMovingResidueOffCurve.curveAdjunction_bijective_of_disjoint
      W.affine t ht W.frame hdisj
  · exact CycleQ2LiteralMovingResidueSmoothChart.curveAdjunction_bijective_of_basis t ht W.frame
      W.affine (rowBasis t s W.frame hs) (rowBasis_zero t s W.frame hs)
      (exteriorSection_bijective t s W.frame hs)

/-- The canonical map, equipped with its actual inverse on a smooth moving member. -/
def curveResidueIso (hc : RowCover t) :
    imageCurveForms t ≅ CycleQ2LiteralMovingResidueExact.residueQuotient t := by
  letI := curveResidue_isIso t ht hc
  exact asIso (curveResidue t ht)

/-- The same independent coefficient vector used for the literal smooth
family has invertible adjunction along the actual closed immersion. -/
theorem curveResidue_isIso_of_independent (hi : AlgebraicIndependent ℚ t) :
    IsIso (curveResidue t ht) :=
  curveResidue_isIso t ht (CycleQ2LiteralResidueRowCover.of_algebraicIndependent t hi)

theorem exists_smooth_curveResidue_isIso :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧ t ≠ 0 ∧
      ∃ ht : ∀ i, ChartRegular t i, IsIso (curveResidue t ht) := by
  obtain ⟨t,hi,hn,ht,_⟩ := CycleQ2LiteralAbelJacobiChartRegular.exists_independent_chartRegular
  exact ⟨t,hi,hn,ht,curveResidue_isIso_of_independent t ht hi⟩

end CycleQ2LiteralMovingResidueSmooth
end

#print axioms CycleQ2LiteralMovingResidueSmooth.curveResidue_isIso
#print axioms CycleQ2LiteralMovingResidueSmooth.curveResidueIso

#print axioms CycleQ2LiteralMovingResidueSmooth.exists_smooth_curveResidue_isIso
