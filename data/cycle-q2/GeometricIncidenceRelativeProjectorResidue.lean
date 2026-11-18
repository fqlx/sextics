import Proposal.GeometricIncidenceRelativeCechMatrix
import Proposal.GeometricIncidenceFirstOrderCanonicalH2
import Proposal.GeometricFamilyDeformation

/-!
# Relative incidence image-line obstruction and its Laurent coefficient

The actual incidence matrix has a rank-one projector on each of the three
coordinate localizations. Lift those projectors in the deformation of the
sextic by the ambient test, restrict to the triple open, and extract the
scalar of the multiplication defect on their common image. Multiplication
by the actual time derivative of the incidence cubic gives a regular
Laurent coefficient in the parameter algebra.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
namespace CycleQ2IncidenceRelativeProjectorResidue

open MvPolynomial CycleQ2IncidenceUniversalChart CycleQ2GeometricSeedNormalizedCoordinates CycleQ2IncidenceNormalForm CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceCanonicalResidue CycleQ2IncidenceRelativeCechMatrix
  CycleQ2IncidenceFirstOrderTrace CycleQ2IncidenceFirstOrderCanonicalH2
  CycleQ2UniversalSurface CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions
  CycleQ2GeometricUniversalSurfaceFirstOrder CycleQ2GeometricRankOneImage
  CycleQ2GeometricProjectorDefect CycleQ2RelativeCanonicalLaurentTrace

abbrev R := ParameterAlgebra
abbrev Face := Finset (Fin 3)

/-- The inverse leading coefficient compensates for normalizing the raw sextic. -/
def leadingUnit : Rˣ := Units.map incidenceChart.toMonoidHom (leading_coefficients_units ℂ).2.unit

def test : MvPolynomial (Fin 5) R := C (↑leadingUnit⁻¹ : R) * (X 2 * X 3 ^ 3 * X 4)

theorem test_unscaled : C (leadingUnit : R) * test = X 2 * X 3 ^ 3 * X 4 := by
  rw [test, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

theorem test_marked : MvPolynomial.map seedMap test = CycleQ2NormalConnecting.derivativeA := by
  have he : Units.map seedMap.toMonoidHom leadingUnit = 1 := by
    apply Units.ext
    exact (RingHom.congr_fun seedMap_incidenceChart ((leading_coefficients_units ℂ).2.unit : ParameterRing ℂ)).trans
      (seed_sexticLeadingUnit ℂ 57 Complex.I)
  have hi : seedMap (↑leadingUnit⁻¹ : R) = 1 := by
    change (((Units.map seedMap.toMonoidHom leadingUnit)⁻¹ : ℂˣ) : ℂ) = 1
    rw [he, inv_one, Units.val_one]
  simp only [test, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, map_pow, hi, map_one, one_mul]
  rfl

def velocityCubic : MvPolynomial (Fin 5) R :=
  fullInvariantPolynomial 3 (fun j => timeDerivation (incidencePoint (Sum.inl j)))

theorem velocityCubic_marked : MvPolynomial.map seedMap velocityCubic = firstOrderWeightedCubic.val := by
  rw [velocityCubic, map_fullInvariantPolynomial]
  rfl

abbrev Thick := LocalSurfaceDeformation R cubic sextic test
abbrev reduction (s : Face) := localSurfaceReduction R cubic sextic test s
abbrev coefficients (s : Face) := localSurfaceCoefficients R cubic sextic test s
abbrev Entries (S : Type) := Matrix (Fin 3) (Fin 3) S

private theorem lift_exists (i : Fin 3) : ∃ e : Entries (Thick {i}), IsIdempotentElem e ∧
    (reduction {i}).mapMatrix e = projectorMatrix (matrix {i}) (weights i) :=
  exists_localSurface_image_projector R cubic sextic test {i} (matrix {i}) (matrix_minors {i})
    (weights i) (weights_sum i)

def liftProjector (i : Fin 3) : Entries (Thick {i}) := (lift_exists i).choose

theorem liftProjector_idempotent (i : Fin 3) : IsIdempotentElem (liftProjector i) :=
  (lift_exists i).choose_spec.1

theorem liftProjector_reduction (i : Fin 3) :
    (reduction {i}).mapMatrix (liftProjector i) = projectorMatrix (matrix {i}) (weights i) :=
  (lift_exists i).choose_spec.2

def restrictedWeights (s : Face) (i : s) (b : Fin 3 × Fin 3) :=
  restriction R cubic sextic (Finset.singleton_subset_iff.mpr i.property) (weights i.val b)

private theorem restrictedWeights_sum (s : Face) (i : s) :
    ∑ b, restrictedWeights s i b * matrix s b.1 b.2 = 1 :=
  weights_restrict_sum i.val i.property

def restrictedProjector (s : Face) (i : s) : Entries (Thick s) :=
  (localSurfaceRestriction R cubic sextic test (Finset.singleton_subset_iff.mpr i.property)).mapMatrix
    (liftProjector i.val)

theorem restrictedProjector_idempotent (s : Face) (i : s) :
    IsIdempotentElem (restrictedProjector s i) :=
  (liftProjector_idempotent i.val).map (localSurfaceRestriction R cubic sextic test _).mapMatrix

theorem restrictedProjector_reduction (s : Face) (i : s) :
    (reduction s).mapMatrix (restrictedProjector s i) = projectorMatrix (matrix s) (restrictedWeights s i) := by
  let h : {i.val} ⊆ s := Finset.singleton_subset_iff.mpr i.property
  let f := restriction R cubic sextic h
  have he : (reduction s).mapMatrix (restrictedProjector s i) =
      (((reduction {i.val}).mapMatrix (liftProjector i.val)).map f) := by
    ext a b
    exact localSurfaceReduction_restriction R cubic sextic test h _
  rw [he, liftProjector_reduction, projectorMatrix_map, matrix_restrict h]
  rfl

/-- The scalar of the actual transition defect, on the image of the original incidence matrix. -/
def obstruction (s : Face) (i j k : s) : Local s :=
  scalarCochain (reduction s) ((coefficients s).matrixCoefficients (Fin 3)) (matrix s) (matrix_minors s)
    (restrictedWeights s) (restrictedWeights_sum s) (restrictedProjector s)
    (restrictedProjector_reduction s) (restrictedWeights s i) i j k

theorem obstruction_cocycle (s : Face) (p i j k l : s) :
    let c := scalarCochain (reduction s) ((coefficients s).matrixCoefficients (Fin 3)) (matrix s)
      (matrix_minors s) (restrictedWeights s) (restrictedWeights_sum s) (restrictedProjector s)
      (restrictedProjector_reduction s) (restrictedWeights s p)
    c j k l - c i k l + c i j l - c i j k = 0 :=
  scalarCochain_cocycle (reduction s) ((coefficients s).matrixCoefficients (Fin 3)) (matrix s)
    (matrix_minors s) (restrictedWeights s) (restrictedWeights_sum s) (restrictedProjector s)
    (restrictedProjector_idempotent s) (restrictedProjector_reduction s) (restrictedWeights s p) i j k l

/-- The time cubic multiplies the obstruction of the ambient-test deformation. -/
def cupRepresentative : Triple :=
  algebraMap (SurfaceRing R cubic sextic) (Local Finset.univ)
    (Ideal.Quotient.mk (surfaceIdeal R cubic sextic) velocityCubic) *
      obstruction Finset.univ ⟨0,Finset.mem_univ _⟩ ⟨1,Finset.mem_univ _⟩ ⟨2,Finset.mem_univ _⟩

/-- This coefficient is a regular element of the actual étale parameter algebra. -/
def regularCoefficient : R := residue cubic sextic cupRepresentative

theorem regularCoefficient_marked : seedMap regularCoefficient =
    residue (CycleQ2GeometricSeedNormalizedCoordinates.cubicCoefficients 57)
      (CycleQ2GeometricSeedNormalizedCoordinates.sexticCoefficients 57) (atMark cupRepresentative) :=
  (atMark_residue cupRepresentative).symm

end CycleQ2IncidenceRelativeProjectorResidue
end

#print axioms CycleQ2IncidenceRelativeProjectorResidue.restrictedProjector_reduction
#print axioms CycleQ2IncidenceRelativeProjectorResidue.obstruction_cocycle
#print axioms CycleQ2IncidenceRelativeProjectorResidue.regularCoefficient_marked
