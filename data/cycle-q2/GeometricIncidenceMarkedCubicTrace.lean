import Proposal.GeometricIncidenceMarkedCoefficientSections
import Proposal.GeometricMarkedProjectorDegree
import Proposal.GeometricIncidenceRelativeProjectorResidue

/-!
# The retained relative coefficient as a trace on the marked projective surface

The original cubic time velocity at the marked point multiplies the
degree-zero part of the genuine rank-one projector obstruction. The
normalized canonical trace on the projective surface evaluates this
class to the specialization of the regular relative coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedCubicTrace

open CategoryTheory Opposite CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceCanonicalResidue CycleQ2RelativeCanonicalLaurentTrace
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2IncidenceRelativeProjectorResidue
  CycleQ2UniversalSurface CycleQ2GradedLocalizationProjection
  CycleQ2GeometricSurfaceCoordinates CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCoordinateCohomology
  CycleQ2GeometricHomogeneousWeight CycleQ2CanonicalCoordinateH2 CycleQ2CanonicalCoordinateCoefficients
  CycleQ2LiteralCotangentTrace CycleQ2CanonicalResidueNonzero CycleQ2CoordinateCechTrace
  CycleQ2MarkedProjectorDegree CycleQ2IncidenceMarkedCoefficientSections

private abbrev Coord := CoordinateLocal 57 1 Finset.univ

theorem marked_cubic_trace (p : MvPolynomial (Fin 5) ParameterAlgebra) (v : WeightedCubic)
    (hv : MvPolynomial.map seedMap p = v.val) (x : CycleQ2IncidenceMarkedCoefficientSections.Local Finset.univ) :
    seedMap (residue cubic sextic (algebraMap _ (CycleQ2IncidenceMarkedCoefficientSections.Local Finset.univ)
      (Ideal.Quotient.mk (surfaceIdeal ParameterAlgebra cubic sextic) p) * x)) =
      algebraicTrace (canonicalConnecting (cubicTripleSection v
        (degreeZero (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 Finset.univ) (markedCone Finset.univ x)))) := by
  rw [markedCone_residue, map_mul, markedCone_polynomial, hv, algebraicTrace_eq]
  change localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
    (algebraMap _ Coord (quotientMap 57 1 v.val) * markedCone Finset.univ x) =
      localCoefficient 57 Finset.univ (2,2) (fun _ => -1) (canonicalCoefficient _)
  rw [canonicalCoefficient_cubicTripleSection, Algebra.smul_def, ← residue_degreeThree]
  exact congrArg (localCoefficient 57 Finset.univ (2,2) (fun _ => -1))
    (homogeneous_mul_zero_projection (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 Finset.univ)
      (surfaceQuotient_mem_grade 57 1 v.property) (markedCone Finset.univ x))

def markedObstruction : HomogeneousCoordinateTop 57 :=
  degreeZero (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 Finset.univ)
    (markedCone Finset.univ (obstruction Finset.univ ⟨0,by simp⟩ ⟨1,by simp⟩ ⟨2,by simp⟩))

theorem regularCoefficient_trace :
    seedMap regularCoefficient =
      algebraicTrace (canonicalConnecting (cubicTripleSection firstOrderWeightedCubic markedObstruction)) :=
  marked_cubic_trace velocityCubic firstOrderWeightedCubic velocityCubic_marked _

end CycleQ2IncidenceMarkedCubicTrace
end

#print axioms CycleQ2IncidenceMarkedCubicTrace.regularCoefficient_trace
