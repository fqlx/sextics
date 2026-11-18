import Proposal.GeometricIncidenceRelativeProjectorResidue
import Proposal.GeometricRelativeAmbientTestBaseChange
import Proposal.GeometricProjectorCochainSpecialization

/-!
# Specialization of the actual incidence projector obstruction

Specialization acts on the original local lifts, the matrix, the time
cubic, and the epsilon coefficient. Consequently the regular element of
the incidence algebra computes the same scalar defect on every fiber.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceRelativeProjectorSpecialization

open CycleQ2IncidenceRelativeProjectorResidue CycleQ2IncidenceCanonicalResidue
  CycleQ2IncidenceRelativeCechMatrix CycleQ2IncidenceEtaleParameter
  CycleQ2UniversalSurface CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceCoefficientMap
  CycleQ2GeometricUniversalSurfaceFirstOrder CycleQ2GeometricRankOneImage
  CycleQ2ProjectorCochainSpecialization CycleQ2RelativeAmbientTestBaseChange
  CycleQ2RelativeCanonicalLaurentTrace

variable {S : Type} [CommRing S] [Nontrivial S] (f : R →+* S)

abbrev cubicFiber := fun i => f (cubic i)
abbrev sexticFiber := fun i => f (sextic i)
abbrev testFiber := MvPolynomial.map f test
abbrev closedMap (s : Face) := localMap f cubic sextic s
abbrev deformedMap (s : Face) := thickMap f cubic sextic test s
abbrev fiberReduction (s : Face) := localSurfaceReduction S (cubicFiber f) (sexticFiber f) (testFiber f) s
abbrev fiberCoefficients (s : Face) := localSurfaceCoefficients S (cubicFiber f) (sexticFiber f) (testFiber f) s

def fiberMatrix (s : Face) := (matrix s).map (closedMap f s)
def fiberWeights (s : Face) (i : s) (b : Fin 3 × Fin 3) := closedMap f s (restrictedWeights s i b)
def fiberProjectors (s : Face) (i : s) := (restrictedProjector s i).map (deformedMap f s)

theorem fiberProjector_idempotent (s : Face) (i : s) : IsIdempotentElem (fiberProjectors f s i) :=
  (restrictedProjector_idempotent s i).map (deformedMap f s).mapMatrix

theorem fiber_minors (s : Face) (a b c d : Fin 3) :
    fiberMatrix f s a b * fiberMatrix f s c d = fiberMatrix f s c b * fiberMatrix f s a d := by
  simpa only [fiberMatrix, Matrix.map_apply, map_mul] using congrArg (closedMap f s) (matrix_minors s a b c d)

theorem fiber_cert (s : Face) (i : s) : ∑ b, fiberWeights f s i b * fiberMatrix f s b.1 b.2 = 1 := by
  simpa only [fiberMatrix, fiberWeights, Matrix.map_apply, map_sum, map_mul, map_one] using
    congrArg (closedMap f s) (weights_restrict_sum i.val i.property)

theorem fiberProjector_reduction (s : Face) (i : s) :
    (fiberReduction f s).mapMatrix (fiberProjectors f s i) = projectorMatrix (fiberMatrix f s) (fiberWeights f s i) := by
  have h : (fiberReduction f s).mapMatrix (fiberProjectors f s i) =
      ((reduction s).mapMatrix (restrictedProjector s i)).map (closedMap f s) := by
    ext a b
    exact thickMap_reduce f cubic sextic test s _
  rw [h, restrictedProjector_reduction, projectorMatrix_map]
  rfl

/-- The epsilon obstruction of the specialized rank-one image. -/
def fiberObstruction (s : Face) (i j k : s) :=
  scalarCochain (fiberReduction f s) ((fiberCoefficients f s).matrixCoefficients (Fin 3))
    (fiberMatrix f s) (fiber_minors f s) (fiberWeights f s) (fiber_cert f s) (fiberProjectors f s)
    (fiberProjector_reduction f s) (fiberWeights f s i) i j k

theorem obstruction_specializes (s : Face) (i j k : s) :
    closedMap f s (obstruction s i j k) = fiberObstruction f s i j k :=
  scalarCochain_map (coefficients s) (fiberCoefficients f s) (deformedMap f s) (closedMap f s)
    (thickMap_epsilon f cubic sextic test s) (matrix s) (matrix_minors s) (restrictedWeights s)
    (fun i => weights_restrict_sum i.val i.property) (restrictedProjector s) (restrictedProjector_reduction s)
    (fiberMatrix f s) (fiber_minors f s) (fiberWeights f s) (fiber_cert f s) (fiberProjectors f s)
    (fiberProjector_reduction f s) rfl (fun _ => rfl) (restrictedWeights s i) i j k

def fiberCup : SurfaceLocal S (cubicFiber f) (sexticFiber f) Finset.univ :=
  algebraMap (SurfaceRing S (cubicFiber f) (sexticFiber f)) _
    (Ideal.Quotient.mk _ (MvPolynomial.map f velocityCubic)) *
    fiberObstruction f Finset.univ ⟨0,Finset.mem_univ _⟩ ⟨1,Finset.mem_univ _⟩ ⟨2,Finset.mem_univ _⟩

theorem cup_specializes : closedMap f Finset.univ cupRepresentative = fiberCup f := by
  unfold cupRepresentative fiberCup
  rw [map_mul, obstruction_specializes]
  change localMap f cubic sextic Finset.univ (algebraMap _ _ _) * _ = _
  rw [localMap_algebraMap, surfaceMap_mk]

theorem fiber_residue : residue (cubicFiber f) (sexticFiber f) (fiberCup f) = f regularCoefficient := by
  rw [← cup_specializes]
  exact residue_baseChange cubic sextic f cupRepresentative

end CycleQ2IncidenceRelativeProjectorSpecialization
end

#print axioms CycleQ2IncidenceRelativeProjectorSpecialization.obstruction_specializes
#print axioms CycleQ2IncidenceRelativeProjectorSpecialization.fiber_residue
