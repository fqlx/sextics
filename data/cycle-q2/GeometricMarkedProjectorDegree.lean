import Proposal.GeometricLiteralCanonicalProjectionFrame
import Proposal.GeometricRelativeCanonicalLaurentTrace

/-!
# Projecting the marked projector obstruction to the projective surface

Multiplication by a homogeneous cubic shifts the projection on a localization
by three. The Laurent residue of the marked surface depends only on this
degree-three component, even for an arbitrary lift on its affine cone.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2MarkedProjectorDegree

open CycleQ2GradedLocalizationProjection CycleQ2LiteralCanonicalDegreeProjection

section Graded

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)

theorem homogeneous_mul_projection {k : ℕ} {c : A} (hc : c ∈ 𝒜 k)
    (t : ℕ) (z : Localization.Away f) :
    degreePlus 𝒜 hf (k + t) (algebraMap A (Localization.Away f) c * z) =
      algebraMap A (Localization.Away f) c * degreePlus 𝒜 hf t z := by
  obtain ⟨n, a, rfl⟩ := exists_fraction f z
  have hm (b : A) : algebraMap A (Localization.Away f) c * fraction f n b =
      fraction f n (c * b) := IsLocalization.mul_mk'_eq_mk'_of_mul c b (powerDenominator f n)
  rw [hm, degreePlus_fraction, degreePlus_fraction, hm, Nat.add_assoc]
  congr 1
  exact DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hc

theorem zero_projection (z : Localization.Away f) :
    degreePlus 𝒜 hf 0 z = (degreeZero 𝒜 hf z).val := by
  obtain ⟨n, a, rfl⟩ := exists_fraction f z
  rw [degreePlus_fraction, degreeZero_fraction, projectedFraction_val, zero_add]

theorem homogeneous_mul_zero_projection {k : ℕ} {c : A} (hc : c ∈ 𝒜 k)
    (z : Localization.Away f) :
    degreePlus 𝒜 hf k (algebraMap A (Localization.Away f) c * z) =
      algebraMap A (Localization.Away f) c * (degreeZero 𝒜 hf z).val := by
  simpa only [Nat.add_zero, zero_projection] using homogeneous_mul_projection 𝒜 hf hc 0 z

end Graded

open CategoryTheory Opposite MvPolynomial CycleQ2CartierSurfaceGrading
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricLaurentTop
  CycleQ2GeometricCoordinateWeight CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechLocalization CycleQ2SeedQuotientFiniteFree CycleQ2SegreTangentLocal
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2CoordinateCechTrace
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2

private abbrev topProduct := coordinateProduct 57 1 Finset.univ
private abbrev topRing := CoordinateLocal 57 1 Finset.univ
private abbrev topCoefficient := localCoefficient 57 Finset.univ (2,2) (fun _ => -1)

private theorem fraction_degree_of_residue (n m : ℕ) (a : SurfaceRing 57 1)
    (ha : a ∈ surfaceGrade 57 1 m) (hn : topCoefficient (fraction topProduct n a) ≠ 0) :
    m = 3 + n * 3 := by
  obtain ⟨p,hp,hpa⟩ := ha
  change quotientMap 57 1 p = a at hpa
  subst a
  let q := fraction topProduct n (quotientMap 57 1 p)
  have hfrac : q * algebraMap (SurfaceRing 57 1) topRing (topProduct ^ n) =
      algebraMap (SurfaceRing 57 1) topRing (quotientMap 57 1 p) :=
    IsLocalization.mk'_spec _ _ _
  have hh := congrArg (seedCoordinateEquiv 57 Finset.univ) hfrac
  simp only [map_mul, seedCoordinateEquiv_base, map_pow, seedRingEquiv_coordinateProduct,
    seedRingEquiv_quotient] at hh
  have hh' : seedCoordinateEquiv 57 Finset.univ q *
      algebraMap (SeedRing (57:ℂ) Complex.I) (SeedLocal ℂ (57:ℂ) Complex.I Finset.univ)
        (algebraMap (Base ℂ) (SeedRing (57:ℂ) Complex.I) (baseProduct ℂ Finset.univ ^ n)) =
      algebraMap (SeedRing (57:ℂ) Complex.I) (SeedLocal ℂ (57:ℂ) Complex.I Finset.univ)
        (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF 57 Complex.I)) p) := by
    simpa only [map_pow] using hh
  have hc := congrArg (fun x => localizedCoordinates ℂ (57:ℂ) Complex.I Finset.univ x (2,2)) hh'
  rw [seed_coordinates_mul_base, localizedCoordinates_algebraMap] at hc
  simp only [map_pow, baseToLaurent_baseProduct, T_pow] at hc
  let e : LaurentExponent := fun _ => -1
  have hv := congrArg (fun z : Laurent (R := ℂ) => z.coeff (e + n • openExponent Finset.univ)) hc
  have hn' : (baseToLaurent ℂ ((seedBasis ℂ (57:ℂ) Complex.I).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF 57 Complex.I)) p) (2,2))).coeff
        (e + n • openExponent Finset.univ) ≠ 0 := by
    rw [← hv, mul_comm (T ℂ _), coeff_mul_T, add_sub_cancel_right]
    exact hn
  have hw := globalLaurent_weight ℂ (57:ℂ) Complex.I p m hp (2,2) _ hn'
  have hshift : n • openExponent (Finset.univ : Finset (Fin 3)) = fun _ => (n : ℤ) := by
    funext i
    change n • (if i ∈ (Finset.univ : Finset (Fin 3)) then (1 : ℤ) else 0) = _
    simp
  rw [hshift] at hw
  norm_num [e, shiftedGrade, Fin.sum_univ_three] at hw
  omega

private theorem fraction_add_same (n : ℕ) (a b : SurfaceRing 57 1) :
    fraction topProduct n (a + b) = fraction topProduct n a + fraction topProduct n b := by
  unfold fraction
  rw [IsLocalization.mk'_eq_mul_mk'_one (a + b) (powerDenominator topProduct n),
    IsLocalization.mk'_eq_mul_mk'_one a (powerDenominator topProduct n),
    IsLocalization.mk'_eq_mul_mk'_one b (powerDenominator topProduct n), map_add, add_mul]

/-- The top coefficient of an arbitrary cone section is the top coefficient of
its genuine projective canonical part. -/
theorem residue_degreeThree (q : topRing) :
    topCoefficient (degreeThree Finset.univ (by simp) q) = topCoefficient q := by
  obtain ⟨n,a,rfl⟩ := exists_fraction topProduct q
  simp only [degreeThree, degreePlus_fraction, Finset.card_univ, Fintype.card_fin]
  induction a using DirectSum.Decomposition.inductionOn (surfaceGrade 57 1) with
  | zero => simp [fraction, IsLocalization.mk'_zero]
  | @homogeneous m a =>
    by_cases hi : m = 3 + n * 3
    · rw [← hi, show GradedRing.proj (surfaceGrade 57 1) _ (a : SurfaceRing 57 1) = a from
        DirectSum.decompose_of_mem_same _ a.property]
    · have hp : GradedRing.proj (surfaceGrade 57 1) (3 + n * 3) (a : SurfaceRing 57 1) = 0 :=
        DirectSum.decompose_of_mem_ne _ a.property hi
      rw [hp, show fraction topProduct n 0 = 0 from IsLocalization.mk'_zero _, map_zero]
      exact (not_ne_iff.mp (fun hn => hi (fraction_degree_of_residue n _ a a.property hn))).symm
  | add a b h₁ h₂ =>
    simp only [map_add, fraction_add_same, h₁, h₂]

end CycleQ2MarkedProjectorDegree
end

#print axioms CycleQ2MarkedProjectorDegree.homogeneous_mul_zero_projection
#print axioms CycleQ2MarkedProjectorDegree.residue_degreeThree
