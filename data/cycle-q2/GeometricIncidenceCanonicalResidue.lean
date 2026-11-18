import Proposal.GeometricRelativeCanonicalLaurentTrace
import Proposal.GeometricIncidenceSeedTangent
import Proposal.GeometricIncidenceSeedFiberCover

/-!
# The normalized Laurent trace on the actual incidence surface family

The full cubic and sextic coefficients on the incidence algebra determine
a map from the universal normalized chart. Its composition with the marked
complex point is the original seed specialization, on the entire chart.
The normalized triple-localization residue therefore specializes to the
computed trace of each marked canonical section represented by that specialization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IncidenceCanonicalResidue
open MvPolynomial AlgebraicGeometry Opposite
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceTraceGeometry
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedTangent CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceGenericPointSemantics
  CycleQ2UniversalSurfaceNormalization CycleQ2UniversalSurface CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceCoefficientMap CycleQ2GeometricSeedNormalizedCoordinates
  CycleQ2RelativeCanonicalLaurentTrace

private theorem leading_unit : IsUnit (aeval incidencePoint (leadingProduct ℂ)) :=
  tracePoint_leading_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint

/-- The map remembers all incidence coordinates, including the determinantal data. -/
def incidenceChart : ParameterRing ℂ →+* ParameterAlgebra :=
  IsLocalization.Away.lift (leadingProduct ℂ) (g := (aeval incidencePoint).toRingHom) leading_unit

private theorem incidenceChart_polynomial (p : ParameterPolynomial ℂ) :
    incidenceChart (algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ) p) = aeval incidencePoint p :=
  IsLocalization.Away.lift_eq (leadingProduct ℂ) leading_unit p

theorem seedMap_incidenceChart : seedMap.comp incidenceChart = (seedSpecialization ℂ 57 Complex.I).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (leadingProduct ℂ))
  apply RingHom.ext
  intro p
  change seedMap (incidenceChart (algebraMap _ _ p)) = seedSpecialization ℂ 57 Complex.I (algebraMap _ _ p)
  rw [incidenceChart_polynomial, seedMap_polynomial, seedSpecialization, specialization_polynomial]
  rfl

def cubic (i : FullCubicTailIndex) : ParameterAlgebra := incidenceChart (universalCubicTail ℂ i)
def sextic (i : FullSexticTailIndex) : ParameterAlgebra := incidenceChart (universalSexticTail ℂ i)

theorem marked_cubic : (fun i => seedMap (cubic i)) = cubicCoefficients 57 :=
  funext fun i => RingHom.congr_fun seedMap_incidenceChart (universalCubicTail ℂ i)

theorem marked_sextic : (fun i => seedMap (sextic i)) = sexticCoefficients 57 :=
  funext fun i => RingHom.congr_fun seedMap_incidenceChart (universalSexticTail ℂ i)

theorem actual_surface_ideal : pointEquations incidencePoint = surfaceIdeal ParameterAlgebra cubic sextic := by
  have h₃ : (fun j => incidenceChart (cubicCoefficient ℂ j)) = pointCubic incidencePoint := by
    funext j
    unfold cubicCoefficient
    rw [incidenceChart_polynomial, aeval_X]
    rfl
  have h₆ : (fun j => incidenceChart (sexticCoefficient ℂ j)) = pointSextic incidencePoint := by
    funext j
    unfold sexticCoefficient
    rw [incidenceChart_polynomial, aeval_X]
    rfl
  rw [pointEquations, pointEquationH, pointEquationF, pointMap_familyH, pointMap_familyF, ← h₃, ← h₆]
  exact mapped_universalIdeal_normalized ℂ incidenceChart

abbrev Triple := SurfaceLocal ParameterAlgebra cubic sextic Finset.univ

private def changeTriple {h₁ h₂ : FullCubicTailIndex → ℂ} {f₁ f₂ : FullSexticTailIndex → ℂ}
    (eh : h₁ = h₂) (ef : f₁ = f₂) (x : SurfaceLocal ℂ h₁ f₁ Finset.univ) :
    SurfaceLocal ℂ h₂ f₂ Finset.univ := eh ▸ ef ▸ x

private theorem residue_changeTriple {h₁ h₂ : FullCubicTailIndex → ℂ} {f₁ f₂ : FullSexticTailIndex → ℂ}
    (eh : h₁ = h₂) (ef : f₁ = f₂) (x : SurfaceLocal ℂ h₁ f₁ Finset.univ) :
    residue h₂ f₂ (changeTriple eh ef x) = residue h₁ f₁ x := by cases eh; cases ef; rfl

def atMark (x : Triple) : NormalizedLocal 57 Finset.univ :=
  changeTriple marked_cubic marked_sextic (localMap seedMap cubic sextic Finset.univ x)

theorem atMark_residue (x : Triple) :
    residue (cubicCoefficients 57) (sexticCoefficients 57) (atMark x) = seedMap (residue cubic sextic x) := by
  rw [atMark, residue_changeTriple, residue_baseChange]

open CycleQ2CanonicalCoordinateH2 CycleQ2CanonicalCoordinateCoefficients CycleQ2LiteralCotangentTrace

theorem represented_canonical_trace (x : Triple) (s : CycleQ2CanonicalCoordinateH2.CanonicalSheaf.obj.obj (op CycleQ2CanonicalCoordinateH2.TripleOpen))
    (hx : atMark x = normalizedCoordinateEquiv 57 Finset.univ (canonicalCoefficient s)) :
    seedMap (residue cubic sextic x) = algebraicTrace (canonicalConnecting s) := by
  rw [← atMark_residue, hx, marked_canonicalSection]

/-- A relative representative of a marked class with nonzero trace cuts out a
principal open containing this marked prime in the incidence parameter scheme. -/
theorem mark_mem_residueOpen (x : Triple) (s : CycleQ2CanonicalCoordinateH2.CanonicalSheaf.obj.obj (op CycleQ2CanonicalCoordinateH2.TripleOpen))
    (hx : atMark x = normalizedCoordinateEquiv 57 Finset.univ (canonicalCoefficient s))
    (hn : algebraicTrace (canonicalConnecting s) ≠ 0) :
    CycleQ2IncidenceSeedFiberCover.seedBasePoint ∈ PrimeSpectrum.basicOpen (residue cubic sextic x) := by
  rw [PrimeSpectrum.mem_basicOpen, CycleQ2IncidenceSeedFiberCover.seedBasePoint,
    CycleQ2IncidenceChartFiberScheme.seedParameterMorphism, Spec.map_apply,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change seedMap (residue cubic sextic x) ∉ (default : Spec (CommRingCat.of ℂ)).asIdeal
  rw [represented_canonical_trace x s hx]
  exact fun hm => (default : Spec (CommRingCat.of ℂ)).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (isUnit_iff_ne_zero.mpr hn))

end CycleQ2IncidenceCanonicalResidue
end

#print axioms CycleQ2IncidenceCanonicalResidue.actual_surface_ideal
#print axioms CycleQ2IncidenceCanonicalResidue.mark_mem_residueOpen
