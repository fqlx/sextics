import Proposal.GeometricLiteralCoordinateTwistPrimitives
import Proposal.GeometricCoordinateCechTrace

/-!
# Laurent weight of negative projective twists

The coordinate unit used to encode a section multiplies its Laurent coefficients
by a single monomial. Multiplication by its nth power recovers the weight-zero
projective section from a representative of twist −n. Thus every nonzero
coefficient of that representative has weight −n on its original chart.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNegativeTwistWeight

open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2SeedProjectiveImageCocycle CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricLaurentTop CycleQ2CoordinateCechTrace
  CycleQ2LiteralCoordinateTwistPrimitives CycleQ2SurfaceSectionCoefficients
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2GeometricHomogeneousWeight CycleQ2SeedCechThreeOpen CycleQ2SegreTangentLocal
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

private theorem section_weight (I : Finset (Fin 3)) (hI : I.Nonempty) (a : Γ(Surface,U I)) :
    sectionCoefficient 57 1 I hI a ∈ coordinateLocalWeight 57 0 I := by
  let h := Finset.subset_univ I
  let b := Surface.presheaf.map (homOfLE (coordinateIntersection_mono 57 1 h)).op a
  have hb : sectionCoefficient 57 1 Finset.univ (by simp) b ∈ coordinateLocalWeight 57 0 Finset.univ :=
    (mem_coordinateLocalWeight_iff 57 0 _ _).mpr (homogeneous_coordinate_weight 57
      ((coordinateSections 57 1 Finset.univ (by simp)).symm b))
  have he := (sectionCoefficient_restrict 57 1 hI (by simp) h a).symm
  change coordinateRestriction 57 1 h (sectionCoefficient 57 1 I hI a) =
    sectionCoefficient 57 1 Finset.univ (by simp) b at he
  rw [← he] at hb
  exact (mem_coordinateLocalWeight_iff 57 0 I _).mpr (fun ab e hn =>
    (mem_coordinateLocalWeight_iff 57 0 Finset.univ _).mp hb ab e
      (by rwa [coordinateLaurent_restriction]))

private theorem coordinate_power_coeff (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (q : cone I) (n : ℕ) (ab : ShiftIndex) (e : LaurentExponent) :
    (coordinateLaurent 57 I (q * (xUnit I i hi : cone I) ^ n) ab).coeff
        (e + n • openExponent {i}) = (coordinateLaurent 57 I q ab).coeff e := by
  have hx : seedRingEquiv 57 (coordinateElement 57 1 i) =
      algebraMap (Base ℂ) (SeedRing (57:ℂ) Complex.I) (X i) := by
    simpa only [coordinateProduct, baseProduct, Finset.prod_singleton] using
      seedRingEquiv_coordinateProduct (57:ℂ) {i}
  have hp : (seedCoordinateEquiv 57 I (xUnit I i hi : cone I)) ^ n =
      algebraMap (SeedRing (57:ℂ) Complex.I) (SeedLocal ℂ (57:ℂ) Complex.I I)
        (algebraMap (Base ℂ) (SeedRing (57:ℂ) Complex.I) ((X i)^n)) := by
    rw [xUnit, IsUnit.unit_spec, seedCoordinateEquiv_base, hx, map_pow, map_pow]
  change (localizedCoordinates ℂ (57:ℂ) Complex.I I
    (seedCoordinateEquiv 57 I (q * (xUnit I i hi : cone I) ^ n)) ab).coeff _ = _
  rw [map_mul, map_pow, hp,
    seed_coordinates_mul_base, map_pow, baseToLaurent_X, T_pow, mul_comm (T ℂ _),
    coeff_mul_T, add_sub_cancel_right]
  rfl

/-- Every regular section on the degree-zero projective chart becomes a
weight-minus-n cone coefficient after the specified inverse nth power. -/
theorem encode_neg_weight (n : ℕ) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i : Fin 3) (hi : i ∈ I) (a : Γ(Surface,U I)) :
    encode (-(n : ℤ)) I hI i hi a ∈ coordinateLocalWeight 57 (-(n : ℤ)) I := by
  let u := xUnit I i hi
  let q := encode (-(n : ℤ)) I hI i hi a
  have hclear : q * (u : cone I) ^ n = sectionCoefficient 57 1 I hI a := by
    change (↑(u ^ (-(n : ℤ))) * sectionCoefficient 57 1 I hI a) * (u : cone I)^n = _
    rw [mul_right_comm, zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, Units.inv_mul, one_mul]
  apply (mem_coordinateLocalWeight_iff 57 (-(n : ℤ)) I _).mpr
  intro ab e hn
  have he := coordinate_power_coeff I i hi q n ab e
  change (coordinateLaurent 57 I (q * (u : cone I)^n) ab).coeff _ = _ at he
  rw [hclear] at he
  have hw := (mem_coordinateLocalWeight_iff 57 0 I _).mp (section_weight I hI a)
    ab (e + n • openExponent {i}) (he ▸ hn)
  have hs : (shiftedGrade ab (e + n • openExponent {i})).1 = (shiftedGrade ab e).1 + n := by
    simp only [shiftedGrade, Pi.add_apply, Finset.sum_add_distrib, nsmul_eq_mul]
    simp [add_assoc]
    change ∑ x : Fin 3, (n : ℤ) * (if x ∈ ({i} : Finset (Fin 3)) then 1 else 0) = n
    simp [mul_ite]
  rw [hs] at hw
  omega

theorem encode_neg_four_weight (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i : Fin 3) (hi : i ∈ I) (a : Γ(Surface,U I)) :
    encode (-4) I hI i hi a ∈ coordinateLocalWeight 57 (-4) I :=
  encode_neg_weight 4 I hI i hi a

end CycleQ2LiteralNegativeTwistWeight

end

#print axioms CycleQ2LiteralNegativeTwistWeight.encode_neg_four_weight
