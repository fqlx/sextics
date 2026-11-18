import Proposal.SolutionSupport05Part03
import Proposal.GeometricCoordinateCechTrace
import Proposal.GeometricCartierOrbitCompatibility
import Proposal.GeometricLiteralMovingDivisorOrbitFrames

/-!
# Negative-degree sections on the three seed translates

On each cyclic character, a compatible family modulo the original orbit
ideal restricts to a single polynomial on the original seed curve. If its
degree is negative the polynomial vanishes. The original orbit-ideal
membership test then makes all three representatives zero in the quotient.
The same calculation gives primitives inside the ideal for the negative
Čech one-cocycles on the three seed coordinate charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitNegativeSections

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2CurveRestriction
  CycleQ2CurveQuotientFiniteFree CycleQ2CurveQuotientGrading
  CycleQ2SeedLinkageCechVanishing CycleQ2SeedCechThreeOpen

theorem curvePolynomial_eq_zero_of_negative_degree {R : Type*} [CommRing R]
    (p : CurvePoly R) (d : ℤ) (hp : SignedHomogeneous R p d) (hd : d < 0) :
    p = 0 := by
  by_contra h
  obtain ⟨e, he⟩ := exists_coeff_ne_zero h
  exact hd.not_ge ((hp e he) ▸ Int.natCast_nonneg (ordinaryDegree e))

private theorem localGrade_res {s t : Finset (Fin 3)} (h : s ⊆ t) (g : LaurentGrade)
    (q : Local s) (hg : localGrade s g q) : localGrade t g (res h q) := by
  intro ab
  exact (CycleQ2SeedCechRestrictions.coordinates_restriction ℂ (57:ℂ) Complex.I h q ab) ▸ hg ab

/-- Degree-wise vanishing in the actual quotients by the three-component seed ideal.
    It suffices to match the sections modulo that ideal on the two indicated overlaps. -/
theorem negative_family_mem_ideal (side : Side) (g : LaurentGrade) (hd : g.1 < 0)
    (q : (i : Fin 3) → Local {i}) (hg : ∀ i, localGrade {i} g (q i))
    (h02 : res (s := {2}) (t := {0,2}) (by decide) (q 2) -
      res (s := {0}) (t := {0,2}) (by decide) (q 0) ∈ localIdeal side {0,2})
    (h12 : res (s := {2}) (t := {1,2}) (by decide) (q 2) -
      res (s := {1}) (t := {1,2}) (by decide) (q 1) ∈ localIdeal side {1,2}) :
    ∀ i, q i ∈ localIdeal side {i} := by
  have pair {i j : Fin 3}
      (h : res (s := {j}) (t := {i,j}) (by simp) (q j) -
        res (s := {i}) (t := {i,j}) (by simp) (q i) ∈ localIdeal side {i,j}) :
      restrictCurve side {i,j} (res (s := {i}) (by simp) (q i)) =
        restrictCurve side {i,j} (res (s := {j}) (by simp) (q j)) := by
    have hv := (mem_iff_restriction_zero side {i,j} (by simp) _ g
      (localGrade_sub _ _ _ _ (localGrade_res _ _ _ (hg j)) (localGrade_res _ _ _ (hg i)))).mp h
    rw [map_sub] at hv
    exact (sub_eq_zero.mp hv).symm
  obtain ⟨p,_,hp,h0,h1,h2⟩ := CycleQ2CurveRestrictionGluing.exists_homogeneous_gluing
    side 57 Complex.I (q 0) (q 1) (q 2) g (hg 0) (pair h02) (pair h12)
  have hz := curvePolynomial_eq_zero_of_negative_degree p g.1 hp hd
  subst p
  simp only [map_zero] at h0 h1 h2
  intro i
  apply (mem_iff_restriction_zero side {i} (Finset.singleton_nonempty i) _ g (hg i)).mpr
  fin_cases i
  · exact h0.symm
  · exact h1.symm
  · exact h2.symm

/-- Every negative homogeneous one-cocycle in the original orbit ideal on the
    seed coordinate charts is the differential of degree-preserving ideal sections. -/
theorem negative_ideal_cech_exact (g : LaurentGrade) (hd : g.1 < 0)
    (p01 : Local {0,1}) (p02 : Local {0,2}) (p12 : Local {1,2})
    (hg01 : localGrade {0,1} g p01) (hg02 : localGrade {0,2} g p02)
    (hg12 : localGrade {1,2} g p12)
    (h02 : p02 ∈ localIdeal .left {0,2}) (h12 : p12 ∈ localIdeal .left {1,2})
    (hc : res (t := Finset.univ) (by decide) p01 -
      res (t := Finset.univ) (by decide) p02 + res (t := Finset.univ) (by decide) p12 = 0) :
    ∃ q : (i : Fin 3) → Local {i}, (∀ i, localGrade {i} g (q i)) ∧
      (∀ i, q i ∈ localIdeal .left {i}) ∧
      p01 = res (by decide) (q 1) - res (by decide) (q 0) ∧
      p02 = res (by decide) (q 2) - res (by decide) (q 0) ∧
      p12 = res (by decide) (q 2) - res (by decide) (q 1) := by
  obtain ⟨q0,q1,q2,hg0,hg1,hg2,e01,e02,e12⟩ :=
    CycleQ2SeedCechRestrictions.coordinateCech_exact ℂ (57:ℂ) Complex.I g
      p01 p02 p12 hg01 hg02 hg12 hc
  let q : (i : Fin 3) → Local {i} := Fin.cases q0 (Fin.cases q1 (Fin.cases q2 (fun i => i.elim0)))
  have hq : ∀ i, localGrade {i} g (q i) := by
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  exact ⟨q, hq, negative_family_mem_ideal .left g hd q hq (e02 ▸ h02) (e12 ▸ h12),
    e01, e02, e12⟩

open CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricLaurentTop
  CycleQ2GeometricCoordinateCharacter CycleQ2CoordinateCechTrace

/-- The original orbit ideal transported to the ordinary surface cone localization. -/
def chartOrbitIdeal (s : Finset (Fin 3)) : Ideal (CoordinateLocal 57 1 s) :=
  (localIdeal .left s).comap (seedCoordinateEquiv 57 s).toRingHom

/-- On a nonempty coordinate intersection the ordinary cone ideal is generated by
    the three literal degree-ten numerators of the projective linkage matrix. -/
theorem chartOrbitIdeal_eq_span (s : Finset (Fin 3)) (hs : s.Nonempty) :
    chartOrbitIdeal s = Ideal.span (Set.range (fun a : Fin 3 =>
      algebraMap (CycleQ2GeometricSeedNormalIdeals.SurfaceRing 57 1) (CoordinateLocal 57 1 s)
        (quotientMap 57 1 (CycleQ2SeedFactorHomogeneous.polynomialLeft (57:ℂ) a)))) := by
  have hmap : chartOrbitIdeal s = (localIdeal .left s).map (seedCoordinateEquiv 57 s).symm.toRingHom :=
    (Ideal.map_symm (I := localIdeal .left s) (seedCoordinateEquiv 57 s)).symm
  rw [hmap]
  change Ideal.map _ (CycleQ2SegreFactorChartExact.factorData s hs).leftIdeal = _
  rw [CycleQ2SeedProjectiveImageTwist.Regrading.leftIdeal_eq_span, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  apply (seedCoordinateEquiv 57 s).injective
  change seedCoordinateEquiv 57 s ((seedCoordinateEquiv 57 s).symm _) = _
  rw [RingEquiv.apply_symm_apply, seedCoordinateEquiv_polynomial] <;> rfl

private theorem coordinateEquiv_res {s t : Finset (Fin 3)} (h : s ⊆ t)
    (q : CoordinateLocal 57 1 s) :
    seedCoordinateEquiv 57 t (coordinateRestriction 57 1 h q) = res h (seedCoordinateEquiv 57 s q) := by
  apply CycleQ2SeedCechLocalizedBasis.localizedCoordinates_injective ℂ (57:ℂ) Complex.I t
  funext ab
  exact (congrFun (coordinateLaurent_restriction 57 h q) ab).trans
    (CycleQ2SeedCechRestrictions.coordinates_restriction ℂ (57:ℂ) Complex.I h _ ab).symm

private theorem projected_localGrade (s : Finset (Fin 3)) (d : ℤ) (χ : ZMod 3)
    (q : CoordinateLocal 57 1 s) (hq : q ∈ coordinateLocalWeight 57 d s) :
    localGrade s (d,χ) (seedCoordinateEquiv 57 s (coordinateProject 57 s χ q)) := by
  intro ab e he
  change (coordinateLaurent 57 s (coordinateProject 57 s χ q) ab).coeff e = 0
  rw [coordinateProject_coordinates, characterPart_coeff]
  by_cases hc : (shiftedGrade ab e).2 = χ
  · rw [if_pos hc]
    exact hq ab e (fun hd => he (Prod.ext hd hc))
  · exact if_neg hc

section CharacterProjection

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageComponents
  CycleQ2SeedLinkageCechVanishing CycleQ2SeedCechThreeOpen
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricCoordinateCharacter
  CycleQ2GeometricLaurentTop CycleQ2GeometricSeedNormalIdeals CycleQ2SegreTangentLocal

private theorem character_mul_on_triple (r : ℂ) (q : CoordinateLocal r 1 Finset.univ)
    (σ : Poly ℂ) (γ χ : ZMod 3) (hσ : σ.IsWeightedHomogeneous characterWeight γ) :
    coordinateProject r Finset.univ χ
      (algebraMap (SurfaceRing r 1) _ (quotientMap r 1 σ) * q) =
      algebraMap (SurfaceRing r 1) _ (quotientMap r 1 σ) *
        coordinateProject r Finset.univ (χ-γ) q := by
  obtain ⟨n,p,rfl⟩ := exists_polynomialFraction r q
  rw [polynomialFraction_mul,coordinateProject_polynomialFraction,
    coordinateProject_polynomialFraction,polynomialFraction_mul]
  apply congrArg (polynomialFraction r n)
  simpa only [add_sub_cancel] using
    CycleQ2WeightedComponent.component_mul_left characterWeight σ p γ (χ-γ) hσ

/-- Multiplication by an eigenvector shifts the projected character, on
every original coordinate localization. -/
theorem coordinateProject_mul_eigenvector (r : ℂ) (s : Finset (Fin 3))
    (q : CoordinateLocal r 1 s) (σ : Poly ℂ) (γ χ : ZMod 3)
    (hσ : σ.IsWeightedHomogeneous characterWeight γ) :
    coordinateProject r s χ (algebraMap (SurfaceRing r 1) _ (quotientMap r 1 σ) * q) =
      algebraMap (SurfaceRing r 1) _ (quotientMap r 1 σ) * coordinateProject r s (χ-γ) q := by
  let h := Finset.subset_univ s
  apply coordinateLaurent_injective r s
  rw [← coordinateLaurent_restriction r h, ← coordinateLaurent_restriction r h
    (algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 s) (quotientMap r 1 σ) *
      coordinateProject r s (χ - γ) q)]
  apply congrArg (coordinateLaurent r Finset.univ)
  rw [← coordinateProject_restriction, map_mul, map_mul, coordinateRestriction_base,
    ← coordinateProject_restriction]
  exact character_mul_on_triple r _ σ γ χ hσ

private theorem linkage_character (side : Side) (r : ℂ) (j : Fin 5) :
    (linkageGenerator side r j).IsWeightedHomogeneous characterWeight (generatorCharacter j) := by
  intro e he
  have hw := congrArg Prod.snd (linkageGenerator_homogeneous side r j he)
  simp only [fullGrading_weight] at hw
  change _ = ((generatorCharacter j : ℕ) : ZMod 3)
  rw [← hw]
  simp [Finsupp.weight_eq_sum, characterWeight, Fin.sum_univ_succ, nsmul_eq_mul] <;> ring

/-- The actual ideal of the three translates is closed under all the
character projections; the five linkage generators each have a fixed character. -/
theorem coordinateProject_mem_localIdeal (side : Side) (s : Finset (Fin 3))
    (χ : ZMod 3) (q : CoordinateLocal 57 1 s)
    (hq : seedCoordinateEquiv 57 s q ∈ localIdeal side s) :
    seedCoordinateEquiv 57 s (coordinateProject 57 s χ q) ∈ localIdeal side s := by
  let e := seedCoordinateEquiv 57 s
  let a (j : Fin 5) := algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s)
    (quotientMap 57 1 (linkageGenerator side (57:ℂ) j))
  have hI : localIdeal side s = Ideal.span (Set.range (fun j => e (a j))) := by
    unfold localIdeal localLinkageIdeal linkageIdeal
    rw [Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext j
    change _ = seedCoordinateEquiv 57 s (algebraMap (SurfaceRing 57 1) _ _)
    rw [seedCoordinateEquiv_base, seedRingEquiv_quotient]
    rfl
  rw [hI] at hq ⊢
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hq
  have he : q = ∑ j, e.symm (c j) * a j := by
    apply e.injective
    simp only [map_sum, map_mul, RingEquiv.apply_symm_apply]
    exact hc.symm
  rw [he]
  change e (coordinateProjectHom 57 s χ _) ∈ _
  rw [map_sum, map_sum]
  apply Ideal.sum_mem
  intro j hj
  change e (coordinateProject 57 s χ (e.symm (c j) * a j)) ∈ _
  rw [mul_comm (e.symm (c j)) (a j)]
  rw [show coordinateProject 57 s χ (a j * e.symm (c j)) =
      a j * coordinateProject 57 s (χ - generatorCharacter j) (e.symm (c j)) from
    coordinateProject_mul_eigenvector 57 s _ _ _ χ (linkage_character side 57 j)]
  let b := coordinateProject 57 s (χ - generatorCharacter j) (e.symm (c j))
  change e (a j * b) ∈ _
  rw [mul_comm (a j) b, map_mul]
  exact (Ideal.span (Set.range (fun k => e (a k)))).mul_mem_left (e b)
    (Ideal.subset_span ⟨j,rfl⟩)

end CharacterProjection

/-- Arbitrary total-weight families on the ordinary coordinate charts vanish modulo the
    orbit ideal in negative degree, including the negative fourth twist of the moving curve. -/
theorem negative_coordinate_family_mem_ideal
    (d : ℤ) (hd : d < 0) (q : (i : Fin 3) → CoordinateLocal 57 1 {i})
    (hg : ∀ i, q i ∈ coordinateLocalWeight 57 d {i})
    (h02 : coordinateRestriction 57 1 (s := {2}) (t := {0,2}) (by decide) (q 2) -
      coordinateRestriction 57 1 (s := {0}) (t := {0,2}) (by decide) (q 0) ∈ chartOrbitIdeal {0,2})
    (h12 : coordinateRestriction 57 1 (s := {2}) (t := {1,2}) (by decide) (q 2) -
      coordinateRestriction 57 1 (s := {1}) (t := {1,2}) (by decide) (q 1) ∈ chartOrbitIdeal {1,2}) :
    ∀ i, q i ∈ chartOrbitIdeal {i} := by
  let component (χ : ZMod 3) (i : Fin 3) := coordinateProject 57 {i} χ (q i)
  have pair (χ : ZMod 3) {i j : Fin 3}
      (h : coordinateRestriction 57 1 (s := {j}) (t := {i,j}) (by simp) (q j) -
        coordinateRestriction 57 1 (s := {i}) (t := {i,j}) (by simp) (q i) ∈ chartOrbitIdeal {i,j}) :
      res (s := {j}) (t := {i,j}) (by simp) (seedCoordinateEquiv 57 {j} (component χ j)) -
        res (s := {i}) (t := {i,j}) (by simp) (seedCoordinateEquiv 57 {i} (component χ i)) ∈
        localIdeal .left {i,j} := by
    have hm := coordinateProject_mem_localIdeal .left {i,j} χ _ h
    have hs (a b : CoordinateLocal 57 1 {i,j}) : coordinateProject 57 {i,j} χ (a - b) =
        coordinateProject 57 {i,j} χ a - coordinateProject 57 {i,j} χ b :=
      (coordinateProjectHom 57 {i,j} χ).map_sub _ _
    change seedCoordinateEquiv 57 {i,j} _ ∈ localIdeal .left {i,j} at hm
    simpa only [component, hs, coordinateProject_restriction, map_sub, coordinateEquiv_res] using hm
  have each (χ : ZMod 3) := negative_family_mem_ideal .left (d,χ) hd
    (fun i => seedCoordinateEquiv 57 {i} (component χ i))
    (fun i => projected_localGrade {i} d χ _ (hg i)) (pair χ h02) (pair χ h12)
  intro i
  rw [← coordinateProject_total 57 {i} (q i)]
  exact Ideal.sum_mem _ (fun χ _ => each χ i)


open AlgebraicGeometry CycleQ2SeedTrace CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedProjectiveImageChart CycleQ2SeedOrbitDivisor
  CycleQ2SeedLinkageComponents CycleQ2SeedLinkageOrbitCover
  CycleQ2LinkageComponentDecomposition CycleQ2LiteralMovingDivisorOrbitFrames

private theorem distinct_cube_roots_square {z w : ℂ} (hz : z^3 = 1)
    (hw : w^3 = 1) (hzw : z ≠ w) : z^2 ≠ w^2 := by
  intro h
  apply hzw
  calc
    z = z * z^3 := by rw [hz, mul_one]
    _ = (z^2)^2 := by ring
    _ = (w^2)^2 := by rw [h]
    _ = w * w^3 := by ring
    _ = w := by rw [hw, mul_one]

theorem affineComponentIdeal_sup_top (i : Fin 3) {z w : ℂ}
    (hz : z^3 = 1) (hw : w^3 = 1) (hzw : z ≠ w) :
    affineComponentIdeal i z ⊔ affineComponentIdeal i w = ⊤ := by
  have hI : Complex.I ≠ (1 : ℂ) := by
    intro h
    have h' := congrArg Complex.im h
    norm_num at h'
  let f := localScalar (57 : ℂ) Complex.I {i}
  have hcov := local_orbit_vertex_cover .left (57 : ℂ) Complex.I (by norm_num)
    Complex.I_ne_zero hI {i} (Finset.singleton_nonempty i)
  rw [localLinkageIdeal_eq_generic] at hcov
  have hloc : localComponent .left (57 : ℂ) Complex.I {i} z ⊔
      localComponent .left (57 : ℂ) Complex.I {i} w = ⊤ := by
    apply components_sup_top _ _ _ _ _ _ _ _ _ _ hcov
    · rw [← map_pow, hz, map_one]
    · rw [← map_pow, hw, map_one]
    · rw [← map_sub]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hzw)).map f
    · rw [← map_pow, ← map_pow, ← map_sub]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (distinct_cube_roots_square hz hw hzw))).map f
  rw [affineComponentIdeal, affineComponentIdeal, ← Ideal.map_sup, hloc, Ideal.map_top]

theorem originalCurveTranslateIdeal_sup_top (i : Fin 3) {z w : ℂ}
    (hz : z^3 = 1) (hw : w^3 = 1) (hzw : z ≠ w) :
    originalCurveTranslateIdeal i z ⊔ originalCurveTranslateIdeal i w = ⊤ := by
  rw [originalCurveTranslateIdeal_eq_component i z hz,
    originalCurveTranslateIdeal_eq_component i w hw, affineComponentIdeal_sup_top i hz hw hzw]

theorem translateIdeal_sup_top (i : Fin 3) (W : Surface.Opens) (hi : W ≤ Patch i)
    {z w : ℂ} (hz : z^3 = 1) (hw : w^3 = 1) (hzw : z ≠ w) :
    translateIdeal i W hi z ⊔ translateIdeal i W hi w = ⊤ := by
  rw [translateIdeal, translateIdeal, ← Ideal.map_sup, originalCurveTranslateIdeal_sup_top i hz hw hzw,
    Ideal.map_top]

end CycleQ2LiteralOrbitNegativeSections

end

#print axioms CycleQ2LiteralOrbitNegativeSections.negative_coordinate_family_mem_ideal
#print axioms CycleQ2LiteralOrbitNegativeSections.translateIdeal_sup_top
#print axioms CycleQ2LiteralOrbitNegativeSections.negative_family_mem_ideal
#print axioms CycleQ2LiteralOrbitNegativeSections.negative_ideal_cech_exact
