import Proposal.GeometricSeedProjectiveImageCocycle
import Proposal.GeometricSurfaceSectionCoefficients
import Proposal.GeometricGradedCechDescent

/-!
# Projection onto an arbitrary integral twist on the literal coordinate cover

A coordinate is invertible in the ordinary cone localization. Multiplying by its
inverse power and extracting the degree-zero component gives an actual
projective section in that chart. The retraction changes by the coordinate
ratio and commutes with restriction, including for negative twists.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCoordinateTwistPrimitives

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
  CycleQ2SeedTrace CycleQ2SeedProjectiveImageCocycle CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCoordinateCohomology
  CycleQ2ProjectiveCoordinateH2 CycleQ2SurfaceCoordinateSections
  CycleQ2SurfaceSectionCoefficients CycleQ2GradedLocalizationProjection
  CycleQ2SeedCechThreeOpen CycleQ2GeometricLaurentTop CycleQ2GeometricSurfaceDehomogenizedCharts

abbrev cone (I : Finset (Fin 3)) := CoordinateLocal 57 1 I
abbrev U (I : Finset (Fin 3)) := coordinateIntersection 57 1 I

def xUnit (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I) : (cone I)ˣ :=
  (coordinateElement_isUnit 57 1 i hi).unit

theorem xUnit_restrict {I J : Finset (Fin 3)} (h : I ⊆ J) (i : Fin 3) (hi : i ∈ I) :
    Units.map (coordinateRestriction 57 1 h).toMonoidHom (xUnit I i hi) = xUnit J i (h hi) := by
  apply Units.ext
  change coordinateRestriction 57 1 h _ = _
  rw [xUnit, IsUnit.unit_spec, xUnit, IsUnit.unit_spec, coordinateRestriction_base]

theorem transition_coefficient (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i j : Fin 3) (hi : i ∈ I) (hj : j ∈ I) :
    Units.map (sectionCoefficient 57 1 I hI).toMonoidHom
      (transitionUnit i j (U I) (intersection_le_chart 57 1 i hi) (intersection_le_chart 57 1 j hj)) *
      xUnit I j hj = xUnit I i hi := by
  apply Units.ext
  change sectionCoefficient 57 1 I hI _ * (xUnit I j hj : cone I) = (xUnit I i hi : cone I)
  have e := sectionCoefficient_homogeneous 57 1 hI j hj 1 (X i.succ.castSucc)
    (show (X i.succ.castSucc : WeightedPoly).IsWeightedHomogeneous weight 1 by
      simpa only [weight_castSucc] using isWeightedHomogeneous_X ℂ weight i.succ.castSucc)
  rw [xUnit, IsUnit.unit_spec, xUnit, IsUnit.unit_spec, coordinateElement_eq 57 1 i]
  change sectionCoefficient 57 1 I hI (coordinatePolynomialSection 57 1 (chartIndex j) _ _ _) * _ = _
  simpa only [pow_one, chartIndex] using e

def encode (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty) (i : Fin 3) (hi : i ∈ I) :
    Γ(Surface, U I) →+ cone I :=
  (AddMonoidHom.mulLeft (↑(xUnit I i hi ^ k) : cone I)).comp (sectionCoefficient 57 1 I hI).toAddMonoidHom

def decode (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty) (i : Fin 3) (hi : i ∈ I) :
    cone I →+ Γ(Surface, U I) :=
  (coordinateSections 57 1 I hI).toAddMonoidHom.comp
    ((degreeZeroAddHom (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 I)).comp
      (AddMonoidHom.mulLeft (↑(xUnit I i hi ^ (-k)) : cone I)))

theorem decode_encode (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty) (i : Fin 3) (hi : i ∈ I)
    (a : Γ(Surface, U I)) : decode k I hI i hi (encode k I hI i hi a) = a := by
  obtain ⟨q,rfl⟩ := (coordinateSections 57 1 I hI).surjective a
  change coordinateSections 57 1 I hI (degreeZero _ (coordinateProduct_mem_grade 57 1 I) (↑(xUnit I i hi ^ (-k)) *
    (↑(xUnit I i hi ^ k) * sectionCoefficient 57 1 I hI _))) = _
  rw [sectionCoefficient_sections, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel,
    zpow_zero, Units.val_one, one_mul, degreeZero_val]

theorem encode_restrict (k : ℤ) {I J : Finset (Fin 3)} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) (i : Fin 3) (hi : i ∈ I) (a : Γ(Surface,U I)) :
    coordinateRestriction 57 1 h (encode k I hI i hi a) =
      encode k J hJ i (h hi) (Surface.presheaf.map (homOfLE (coordinateIntersection_mono 57 1 h)).op a) := by
  change coordinateRestriction 57 1 h (↑(xUnit I i hi ^ k) * sectionCoefficient 57 1 I hI a) =
    ↑(xUnit J i (h hi) ^ k) * sectionCoefficient 57 1 J hJ _
  rw [map_mul, sectionCoefficient_restrict 57 1 hI hJ h]
  congr 1
  exact congrArg Units.val ((map_zpow (Units.map (coordinateRestriction 57 1 h).toMonoidHom)
    (xUnit I i hi) k).trans (congrArg (fun u : (cone J)ˣ => u^k) (xUnit_restrict h i hi)))

theorem decode_restrict (k : ℤ) {I J : Finset (Fin 3)} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) (i : Fin 3) (hi : i ∈ I) (a : cone I) :
    Surface.presheaf.map (homOfLE (coordinateIntersection_mono 57 1 h)).op (decode k I hI i hi a) =
      decode k J hJ i (h hi) (coordinateRestriction 57 1 h a) := by
  change Surface.presheaf.map _ (coordinateSections 57 1 I hI (degreeZero _ (coordinateProduct_mem_grade 57 1 I) _)) = _
  rw [coordinateSections_restrict]
  change coordinateSections 57 1 J hJ (coordinateHomogeneousRestriction 57 1 h _) =
    coordinateSections 57 1 J hJ (degreeZero _ (coordinateProduct_mem_grade 57 1 J) _)
  apply congrArg (coordinateSections 57 1 J hJ)
  unfold coordinateHomogeneousRestriction
  rw [← degreeZero_naturality (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 I)
    (coordinateProduct_mem_grade 57 1 (J \ I)) (coordinateProduct_factor 57 1 h)
    (coordinateProduct_mem_grade 57 1 J) (coordinateRestriction 57 1 h)]
  apply congrArg (degreeZero (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 J))
  change coordinateRestriction 57 1 h (↑(xUnit I i hi ^ (-k)) * a) = _ * _
  rw [map_mul]
  congr 1
  exact congrArg Units.val ((map_zpow (Units.map (coordinateRestriction 57 1 h).toMonoidHom)
    (xUnit I i hi) (-k)).trans (congrArg (fun u : (cone J)ˣ => u^(-k)) (xUnit_restrict h i hi)))

theorem decode_change (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i j : Fin 3) (hi : i ∈ I) (hj : j ∈ I) (a : cone I) :
    decode k I hI i hi a =
      (↑(transitionUnit i j (U I) (intersection_le_chart 57 1 i hi)
        (intersection_le_chart 57 1 j hj) ^ (-k)) : Γ(Surface,U I)) * decode k I hI j hj a := by
  let u := transitionUnit i j (U I) (intersection_le_chart 57 1 i hi) (intersection_le_chart 57 1 j hj)
  let b := (coordinateSections 57 1 I hI).symm ((u ^ (-k) : Γ(Surface,U I)ˣ) : Γ(Surface,U I))
  have h : (↑(xUnit I i hi ^ (-k)) : cone I) = b.val * ↑(xUnit I j hj ^ (-k)) := by
    have e := congrArg (fun q : (cone I)ˣ => q^(-k)) (transition_coefficient I hI i j hi hj).symm
    rw [mul_zpow, ← map_zpow] at e
    exact congrArg Units.val e
  change coordinateSections 57 1 I hI (degreeZero _ (coordinateProduct_mem_grade 57 1 I) (↑(xUnit I i hi ^ (-k)) * a)) = _
  rw [h, mul_assoc, degreeZero_mul_homogeneous, map_mul, RingEquiv.apply_symm_apply]
  rfl

theorem encode_change (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i j : Fin 3) (hi : i ∈ I) (hj : j ∈ I) (a : Γ(Surface,U I)) :
    encode k I hI i hi ((↑(transitionUnit i j (U I) (intersection_le_chart 57 1 i hi)
      (intersection_le_chart 57 1 j hj) ^ (-k)) : Γ(Surface,U I)) * a) = encode k I hI j hj a := by
  let u := transitionUnit i j (U I) (intersection_le_chart 57 1 i hi) (intersection_le_chart 57 1 j hj)
  let φ := Units.map (sectionCoefficient 57 1 I hI).toMonoidHom
  have e : φ u * xUnit I j hj = xUnit I i hi := transition_coefficient I hI i j hi hj
  have eq : xUnit I i hi ^ k * φ (u ^ (-k)) = xUnit I j hj ^ k := by
    rw [← e, mul_zpow, map_zpow, zpow_neg, mul_right_comm, mul_inv_cancel, one_mul]
  change ↑(xUnit I i hi ^ k) * sectionCoefficient 57 1 I hI (_ * a) = _
  rw [map_mul, ← mul_assoc]
  exact congrArg (· * sectionCoefficient 57 1 I hI a) (congrArg Units.val eq)

/-- Native affine-cone primitives for the three ordered coordinate overlaps. -/
theorem cone_first_exact
    (a : cone {0,1}) (b : cone {0,2}) (c : cone {1,2})
    (hc : coordinateRestriction 57 1 (Finset.subset_univ _) a -
      coordinateRestriction 57 1 (Finset.subset_univ _) b +
      coordinateRestriction 57 1 (Finset.subset_univ _) c = 0) :
    ∃ (x : cone {0}) (y : cone {1}) (z : cone {2}),
      a = coordinateRestriction 57 1 (by decide) y - coordinateRestriction 57 1 (by decide) x ∧
      b = coordinateRestriction 57 1 (by decide) z - coordinateRestriction 57 1 (by decide) x ∧
      c = coordinateRestriction 57 1 (by decide) z - coordinateRestriction 57 1 (by decide) y := by
  let A := coordinateLaurent 57 {0,1} a
  let B := coordinateLaurent 57 {0,2} b
  let C := coordinateLaurent 57 {1,2} c
  have he (d : ShiftIndex) : A d - B d + C d = 0 := by
    have h := congrArg (fun p => coordinateLaurent 57 Finset.univ p d) hc
    simpa only [map_add, map_sub, map_zero, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
      coordinateLaurent_restriction, A, B, C] using h
  have h (d : ShiftIndex) := threeOpen_kernel (A d) (B d) (C d)
    (coordinateLaurent_hasPoles 57 _ a d) (coordinateLaurent_hasPoles 57 _ b d)
    (coordinateLaurent_hasPoles 57 _ c d) (he d)
  obtain ⟨x,hx⟩ := (coordinateLaurent_range 57 {0} _).mpr (fun d => (h d).1)
  obtain ⟨y,hy⟩ := (coordinateLaurent_range 57 {1} _).mpr (fun d => (h d).2.1)
  obtain ⟨z,hz⟩ := (coordinateLaurent_range 57 {2} _).mpr (fun d => (h d).2.2.1)
  refine ⟨x,y,z,?_,?_,?_⟩
  · apply coordinateLaurent_injective
    funext d
    rw [map_sub, Pi.sub_apply, coordinateLaurent_restriction, coordinateLaurent_restriction, hx, hy]
    exact (h d).2.2.2.1
  · apply coordinateLaurent_injective
    funext d
    rw [map_sub, Pi.sub_apply, coordinateLaurent_restriction, coordinateLaurent_restriction, hx, hz]
    exact (h d).2.2.2.2.1
  · apply coordinateLaurent_injective
    funext d
    rw [map_sub, Pi.sub_apply, coordinateLaurent_restriction, coordinateLaurent_restriction, hy, hz]
    exact (h d).2.2.2.2.2

end CycleQ2LiteralCoordinateTwistPrimitives

end

#print axioms CycleQ2LiteralCoordinateTwistPrimitives.decode_restrict
#print axioms CycleQ2LiteralCoordinateTwistPrimitives.decode_change

#print axioms CycleQ2LiteralCoordinateTwistPrimitives.cone_first_exact
