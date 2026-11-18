import Proposal.GeometricIncidenceCanonicalResidue
import Proposal.GeometricEtaleIncidenceCurve
import Proposal.GeometricRelativeConstantSection

/-!
# The incidence matrix on the three relative coordinate charts

The same homogeneous incidence matrix restricts to every coordinate
intersection of the normalized surface. Its minors vanish by the incidence
equations, and its entries generate the unit ideal on every nonempty
intersection by the basepoint identity.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

noncomputable section
namespace CycleQ2IncidenceRelativeCechMatrix

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceBasepointOpen CycleQ2IncidenceImageLine
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2UniversalSurface
  CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions
  CycleQ2UniversalSurfaceCoefficientMap CycleQ2IncidenceCanonicalResidue

abbrev Raw := CurveRing (pointMap incidencePoint)
abbrev Surface := SurfaceRing ParameterAlgebra cubic sextic
abbrev Local (s : Finset (Fin 3)) := SurfaceLocal ParameterAlgebra cubic sextic s

/-- Identity on all five variables, modulo the normalized surface equations. -/
def normalize : Raw ≃+* Surface := Ideal.quotEquivOfEq actual_surface_ideal

theorem normalize_mk (p : MvPolynomial (Fin 5) ParameterAlgebra) :
    normalize (curveQuotient (pointMap incidencePoint) p) = Ideal.Quotient.mk _ p :=
  Ideal.quotEquivOfEq_mk _ _

def localize (s : Finset (Fin 3)) : Raw →+* Local s :=
  (algebraMap Surface (Local s)).comp normalize.toRingHom

def matrix (s : Finset (Fin 3)) : Matrix (Fin 3) (Fin 3) (Local s) :=
  fun i j => localize s (curveMatrix (pointMap incidencePoint) i j)

theorem matrix_entry (s : Finset (Fin 3)) (i j : Fin 3) :
    matrix s i j = algebraMap Surface (Local s)
      (Ideal.Quotient.mk _ (pointMatrixPolynomial incidencePoint i j)) := by
  change algebraMap Surface (Local s) (normalize (curveQuotient _
    (MvPolynomial.map _ (familyMatrix i j)))) = _
  rw [normalize_mk, pointMatrixPolynomial_eq]

theorem matrix_restrict {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    (restriction ParameterAlgebra cubic sextic hst).mapMatrix (matrix s) = matrix t := by
  ext i j
  change restriction ParameterAlgebra cubic sextic hst (matrix s i j) = matrix t i j
  rw [matrix_entry, matrix_entry, restriction_algebraMap]

theorem matrix_minors (s : Finset (Fin 3)) (i j k l : Fin 3) :
    matrix s i j * matrix s k l = matrix s k j * matrix s i l := by
  have hc := curveMatrix_cofactors incidencePoint
    CycleQ2EtaleIncidenceCurve.original_incidence_equations CycleQ2EtaleIncidenceCurve.leading_unit
  have hm := CycleQ2SegreLocal.minors_of_cofactors_zero _ hc i j k l
  rw [mul_comm (matrix s k j)]
  simpa only [matrix, map_mul] using congrArg (localize s) hm

private theorem rawWeights (i : Fin 3) :
    ∃ a : Fin 3 × Fin 3 → Raw, ∑ q, a q * curveMatrix (pointMap incidencePoint) q.1 q.2 =
      curveCoordinate (pointMap incidencePoint) (remainingIndex i) ^
        CycleQ2SegreComplexBasepoint.coordinatePower (remainingIndex i) := by
  have hb : IsUnit (pointMap incidencePoint basepointPolynomial) := CycleQ2EtaleIncidenceCurve.basepoint_unit
  have hm := specialized_coordinate_power_mem (pointMap incidencePoint) hb (remainingIndex i)
  unfold entryIdeal at hm
  exact Ideal.mem_span_range_iff_exists_fun.mp hm

private theorem coordinate_unit {s : Finset (Fin 3)} {i : Fin 3} (hi : i ∈ s) :
    IsUnit (localize s (curveCoordinate (pointMap incidencePoint) (remainingIndex i))) := by
  change IsUnit (algebraMap Surface (Local s)
    (normalize (curveQuotient _ (X (remainingIndex i)))))
  rw [normalize_mk]
  have h := surfaceProduct_isUnit ParameterAlgebra cubic sextic (Finset.singleton_subset_iff.mpr hi)
  simp only [baseProduct, Finset.prod_singleton] at h
  change IsUnit (algebraMap Surface (Local s)
    (Ideal.Quotient.mk _ (remainingInclusion ParameterAlgebra (X i)))) at h
  simpa only [remainingInclusion, rename_X] using h

attribute [local irreducible] localize normalize

set_option maxHeartbeats 4000000 in
theorem exists_weights (s : Finset (Fin 3)) (hs : s.Nonempty) :
    ∃ w : Fin 3 × Fin 3 → Local s, ∑ ij, w ij * matrix s ij.1 ij.2 = 1 := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨a, ha⟩ := rawWeights i
  let x := curveCoordinate (pointMap incidencePoint) (remainingIndex i)
  let n := CycleQ2SegreComplexBasepoint.coordinatePower (remainingIndex i)
  have he : ∑ q, localize s (a q) * matrix s q.1 q.2 = (localize s x) ^ n := by
    simpa only [matrix, x, n, map_sum, map_mul, map_pow] using congrArg (localize s) ha
  obtain ⟨u, hu⟩ : IsUnit ((localize s x) ^ n) := (@coordinate_unit s i hi).pow n
  refine ⟨fun q => (↑(u⁻¹) : Local s) * localize s (a q), ?_⟩
  simp only [mul_assoc, ← Finset.mul_sum, he, ← hu, Units.inv_mul]

theorem entries_generate (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => matrix s ij.1 ij.2)) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.mem_span_range_iff_exists_fun.mpr (exists_weights s hs))

/-- Weights for the rank-one projector on each of the three charts. -/
def weights (i : Fin 3) : Fin 3 × Fin 3 → Local {i} :=
  (exists_weights {i} (Finset.singleton_nonempty i)).choose

theorem weights_sum (i : Fin 3) :
    ∑ ij, weights i ij * matrix {i} ij.1 ij.2 = 1 :=
  (exists_weights {i} (Finset.singleton_nonempty i)).choose_spec

/-- The chosen projector weights restrict to a certificate for the very
same matrix on every overlap containing chart `i`. -/
theorem weights_restrict_sum (i : Fin 3) {s : Finset (Fin 3)} (hi : i ∈ s) :
    ∑ ij, restriction ParameterAlgebra cubic sextic (Finset.singleton_subset_iff.mpr hi)
      (weights i ij) * matrix s ij.1 ij.2 = 1 := by
  let φ := restriction ParameterAlgebra cubic sextic (Finset.singleton_subset_iff.mpr hi)
  have he (a b : Fin 3) : φ (matrix {i} a b) = matrix s a b :=
    congrArg (fun M => M a b) (matrix_restrict (Finset.singleton_subset_iff.mpr hi))
  simpa only [map_sum, map_mul, map_one, he] using congrArg φ (weights_sum i)

/-- Base change to the mark recovers the original seed matrix polynomial
entry by entry on every intersection. -/
theorem matrix_seed (s : Finset (Fin 3)) (i j : Fin 3) :
    localMap seedMap cubic sextic s (matrix s i j) =
      algebraMap _ _
        (Ideal.Quotient.mk (surfaceIdeal ℂ (fun k => seedMap (cubic k))
          (fun k => seedMap (sextic k)))
          (pointMatrixPolynomial (seedPoint (57 : ℂ) Complex.I) i j)) := by
  rw [matrix_entry, localMap_algebraMap, surfaceMap_mk,
    CycleQ2RelativeConstantSection.pointMatrixPolynomial_seed]

end CycleQ2IncidenceRelativeCechMatrix
end

#print axioms CycleQ2IncidenceRelativeCechMatrix.matrix_restrict
#print axioms CycleQ2IncidenceRelativeCechMatrix.matrix_minors
#print axioms CycleQ2IncidenceRelativeCechMatrix.weights_sum
#print axioms CycleQ2IncidenceRelativeCechMatrix.matrix_seed
