import Proposal.GeometricHodgeEulerChartBinding
import Proposal.GeometricHodgeEulerOverlap
import Proposal.GeometricHodgeTwistRatios

/-!
# Native projective overlaps in the weight-one affine charts

Sections on the intersection of two coordinate opens identify with the
localization of the first dehomogenized chart at the second coordinate.
Under this identification the homogeneous twist transition is the pivot
unit, and the second chart's coordinates are the weighted affine ratios.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerOverlapBinding

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open CycleQ2GeometricIncidenceProj CycleQ2GenericSexticGradient
open CycleQ2GeometricProjectiveCurve.Twisted (res)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i k : Fin 4)

abbrev intersection := coordinateOpen φ i ⊓ coordinateOpen φ k

private abbrev den := coord φ i.castSucc * coord φ k.castSucc
private abbrev ProductRing := HomogeneousLocalization.Away (grade φ) (den φ i k)

private theorem den_mem : den φ i k ∈ grade φ 2 :=
  SetLike.mul_mem_graded (weightOne_mem_grade φ i) (weightOne_mem_grade φ k)

private theorem pivot_fraction :
    HomogeneousLocalization.Away.isLocalizationElem (weightOne_mem_grade φ i)
      (weightOne_mem_grade φ k) = ratio φ i k.castSucc := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem, ratio, fraction,
    CycleQ2SeedFermatProj.geometricWeight_castSucc, HomogeneousLocalization.Away.val_mk, pow_one]
  rfl

/-- In the first affine chart the second projective open is exactly the principal pivot locus. -/
theorem affineChart_preimage :
    ((affineChart φ i).inv ≫ (coordinateOpen φ i).ι) ⁻¹ᵁ coordinateOpen φ k =
      PrimeSpectrum.basicOpen (coordinate φ i k.castSucc) := by
  have h : (affineChart φ i).inv ≫ (coordinateOpen φ i).ι =
      Spec.map (CommRingCat.ofHom (chartEquiv φ i).toRingEquiv.toRingHom) ≫
        Proj.awayι (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide) :=
    Category.assoc _ _ _
  rw [h, Scheme.Hom.comp_preimage, coordinateOpen,
    Proj.awayι_preimage_basicOpen (𝒜 := grade φ) (weightOne_mem_grade φ i) (by decide)
      (weightOne_mem_grade φ k) (by decide), pivot_fraction]
  change PrimeSpectrum.basicOpen (chartEquiv φ i (ratio φ i k.castSucc)) = _
  rw [chartEquiv_ratio]
  rfl

private def restrictNative : ChartRing φ i →+* ProductRing φ i k :=
  HomogeneousLocalization.awayMap (grade φ) (weightOne_mem_grade φ k) rfl

private theorem restrictNative_isLocalization :
    letI := (restrictNative φ i k).toAlgebra
    IsLocalization.Away (ratio φ i k.castSucc) (ProductRing φ i k) := by
  let := (restrictNative φ i k).toAlgebra
  rw [← pivot_fraction]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (weightOne_mem_grade φ i) (weightOne_mem_grade φ k) rfl (by decide)

private theorem chartEquiv_powers :
    (Submonoid.powers (ratio φ i k.castSucc)).map (chartEquiv φ i).toRingEquiv.toMonoidHom =
      Submonoid.powers (coordinate φ i k.castSucc) := by
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (chartEquiv_ratio φ i k.castSucc)

private def productEquiv : ProductRing φ i k ≃+* overlap φ i k := by
  letI := (restrictNative φ i k).toAlgebra
  letI := restrictNative_isLocalization φ i k
  exact IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (ratio φ i k.castSucc))
    (T := Submonoid.powers (coordinate φ i k.castSucc)) _ _ (chartEquiv φ i).toRingEquiv
    (chartEquiv_powers φ i k)

private theorem productEquiv_restrict (a : ChartRing φ i) :
    productEquiv φ i k (restrictNative φ i k a) =
      algebraMap (chart φ i) (overlap φ i k) (chartEquiv φ i a) := by
  let := (restrictNative φ i k).toAlgebra
  let := restrictNative_isLocalization φ i k
  exact IsLocalization.ringEquivOfRingEquiv_eq (S := ProductRing φ i k) (Q := overlap φ i k)
    (M := Submonoid.powers (ratio φ i k.castSucc)) (T := Submonoid.powers (coordinate φ i k.castSucc))
    (j := (chartEquiv φ i).toRingEquiv) (chartEquiv_powers φ i k) a

private abbrev productOpen := Proj.basicOpen (grade φ) (den φ i k)

private theorem intersection_eq : intersection φ i k = productOpen φ i k :=
  (Proj.basicOpen_mul (grade φ) _ _).symm

def overlapChart : (intersection φ i k).toScheme ≅ Spec (CommRingCat.of (overlap φ i k)) :=
  (threefold φ).isoOfEq (intersection_eq φ i k) ≪≫
    Proj.basicOpenIsoSpec (grade φ) (den φ i k) (den_mem φ i k) (by decide) ≪≫
    Scheme.Spec.mapIso (productEquiv φ i k).toCommRingCatIso.symm.op

private def nativeSections :
    CommRingCat.of (ProductRing φ i k) ≅ Γ(threefold φ, productOpen φ i k) :=
  Proj.basicOpenIsoAway (grade φ) (den φ i k) (den_mem φ i k) (by decide)

private def readAt (V : (threefold φ).Opens) (hV : V = productOpen φ i k) :
    Γ(threefold φ, V) ≃+* overlap φ i k := by
  subst V
  exact (nativeSections φ i k).symm.commRingCatIsoToRingEquiv.trans (productEquiv φ i k)

def overlapSections : Γ(threefold φ, intersection φ i k) ≃+* overlap φ i k :=
  readAt φ i k _ (intersection_eq φ i k)

private theorem readAt_restrict (V : (threefold φ).Opens) (hV : V = productOpen φ i k)
    (hi : V ≤ coordinateOpen φ i) (a : ChartRing φ i) :
    readAt φ i k V hV (res (threefold φ).sheaf hi ((Proj.awayToSection (grade φ) _) a)) =
      algebraMap (chart φ i) (overlap φ i k) (chartEquiv φ i a) := by
  subst V
  have h : res (threefold φ).sheaf hi ((Proj.awayToSection (grade φ) _) a) =
      (nativeSections φ i k).hom (restrictNative φ i k a) :=
    ConcreteCategory.congr_hom
      (Proj.awayMap_awayToSection (grade φ) (weightOne_mem_grade φ k) rfl).symm a
  change productEquiv φ i k ((nativeSections φ i k).inv _) = _
  rw [h, Iso.hom_inv_id_apply, productEquiv_restrict]

theorem overlapSections_restrict (a : ChartRing φ i) :
    overlapSections φ i k
        (res (threefold φ).sheaf inf_le_left ((Proj.awayToSection (grade φ) _) a)) =
      algebraMap (chart φ i) (overlap φ i k) (chartEquiv φ i a) :=
  readAt_restrict φ i k _ _ _ a

theorem overlapSections_normalized {n : ℕ} (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    overlapSections φ i k (CycleQ2HodgeTwistRatios.normalized φ i (quotient φ p)
        (quotient_mem_grade φ p hp) _ inf_le_left) =
      algebraMap (chart φ i) (overlap φ i k) (chartMap φ i (dehom i p)) :=
  (overlapSections_restrict φ i k (fraction φ i n p hp)).trans
    (congrArg (algebraMap (chart φ i) _) (chartEquiv_fraction φ i n p hp))

theorem overlapSections_coordinate (j : Fin 5) :
    overlapSections φ i k (CycleQ2HodgeTwistRatios.normalized φ i (coord φ j)
        (coord_mem_grade φ j) _ inf_le_left) = localCoordinate φ i k j :=
  overlapSections_normalized φ i k (X j) (isWeightedHomogeneous_X R geometricWeight j)

theorem overlapSections_pivot :
    overlapSections φ i k (CycleQ2HodgeTwistRatios.ratio φ i k _ inf_le_left) =
      localCoordinate φ i k k.castSucc := by
  have h (n : ℕ) (hn : n = 1) (hc : coord φ k.castSucc ∈ grade φ n) :
      CycleQ2HodgeTwistRatios.normalized φ i (coord φ k.castSucc) hc
        (intersection φ i k) inf_le_left = CycleQ2HodgeTwistRatios.ratio φ i k _ inf_le_left := by
    subst n
    rfl
  rw [← h _ (CycleQ2SeedFermatProj.geometricWeight_castSucc k) (coord_mem_grade φ k.castSucc)]
  exact overlapSections_coordinate φ i k k.castSucc

def pivotUnit : (overlap φ i k)ˣ where
  val := localCoordinate φ i k k.castSucc
  inv := invPivot φ i k
  val_inv := localCoordinate_mul_invPivot φ i k
  inv_val := (mul_comm _ _).trans (localCoordinate_mul_invPivot φ i k)

theorem overlapSections_transitionUnit :
    Units.map (overlapSections φ i k).toMonoidHom
      (CycleQ2HodgeTwistRatios.transition φ i k _ inf_le_left inf_le_right) = pivotUnit φ i k :=
  Units.ext (overlapSections_pivot φ i k)

theorem overlapSections_otherCoordinate (j : Fin 5) :
    overlapSections φ i k (CycleQ2HodgeTwistRatios.normalized φ k (coord φ j)
      (coord_mem_grade φ j) _ inf_le_right) = overlapMap φ i k (coordinate φ k j) := by
  have h := congrArg (overlapSections φ i k) (CycleQ2HodgeTwistRatios.normalized_change φ i k
    (coord φ j) (coord_mem_grade φ j) _ inf_le_left inf_le_right)
  rw [map_mul, map_pow, overlapSections_coordinate, overlapSections_pivot] at h
  rw [overlapMap_coordinate, ratioCoordinate, h, ← mul_assoc, ← mul_pow,
    mul_comm (invPivot φ i k), localCoordinate_mul_invPivot, one_pow, one_mul]

private def restrictOther : ChartRing φ k →+* ProductRing φ i k :=
  HomogeneousLocalization.awayMap (grade φ) (weightOne_mem_grade φ i) (mul_comm _ _)

private theorem readAt_other (V : (threefold φ).Opens) (hV : V = productOpen φ i k)
    (hk : V ≤ coordinateOpen φ k) (a : ChartRing φ k) :
    readAt φ i k V hV (res (threefold φ).sheaf hk ((Proj.awayToSection (grade φ) _) a)) =
      productEquiv φ i k (restrictOther φ i k a) := by
  subst V
  have h : res (threefold φ).sheaf hk ((Proj.awayToSection (grade φ) _) a) =
      (nativeSections φ i k).hom (restrictOther φ i k a) :=
    ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (grade φ)
      (weightOne_mem_grade φ i) (mul_comm _ _)).symm a
  change productEquiv φ i k ((nativeSections φ i k).inv _) = _
  rw [h, Iso.hom_inv_id_apply]

private theorem restrictOther_coordinate (j : Fin 5) :
    productEquiv φ i k (restrictOther φ i k (ratio φ k j)) =
      overlapMap φ i k (coordinate φ k j) :=
  (readAt_other φ i k _ (intersection_eq φ i k) inf_le_right (ratio φ k j)).symm.trans
    (overlapSections_otherCoordinate φ i k j)

private theorem restrictOther_scalar (c : R) :
    productEquiv φ i k (restrictOther φ i k (algebraMap R (ChartRing φ k) c)) =
      algebraMap R (overlap φ i k) c := by
  have h : restrictOther φ i k (algebraMap R (ChartRing φ k) c) =
      restrictNative φ i k (algebraMap R (ChartRing φ i) c) :=
    (HomogeneousLocalization.awayMap_fromZeroRingHom (grade φ) (weightOne_mem_grade φ i)
      (mul_comm _ _) (coefficient φ c)).trans
      (HomogeneousLocalization.awayMap_fromZeroRingHom (grade φ) (weightOne_mem_grade φ k)
        rfl (coefficient φ c)).symm
  rw [h, productEquiv_restrict, (chartEquiv φ i).commutes]
  exact (IsScalarTower.algebraMap_apply R (chart φ i) (overlap φ i k) c).symm

private theorem restrictOther_eq :
    (productEquiv φ i k).toRingHom.comp (restrictOther φ i k) =
      (overlapMap φ i k).toRingHom.comp (chartEquiv φ k).toRingEquiv.toRingHom := by
  let f := ((productEquiv φ i k).toRingHom.comp (restrictOther φ i k)).comp
    (chartEquiv φ k).symm.toRingEquiv.toRingHom
  have he : f.comp (chartMap φ k).toRingHom = (overlapMap φ i k).toRingHom.comp
      (chartMap φ k).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change productEquiv φ i k (restrictOther φ i k ((chartEquiv φ k).symm
        (chartMap φ k (algebraMap R (MvPolynomial (Fin 4) R) c)))) =
        overlapMap φ i k (chartMap φ k (algebraMap R (MvPolynomial (Fin 4) R) c))
      rw [(chartMap φ k).commutes, (chartEquiv φ k).symm.commutes, restrictOther_scalar,
        (overlapMap φ i k).commutes]
    · intro j
      change productEquiv φ i k (restrictOther φ i k ((chartEquiv φ k).symm (chartMap φ k (X j)))) =
        overlapMap φ i k (chartMap φ k (X j))
      rw [← chartEquiv_ratio_succAbove φ k j, AlgEquiv.symm_apply_apply]
      exact restrictOther_coordinate φ i k (k.castSucc.succAbove j) |>.trans
        (congrArg (overlapMap φ i k) (chartEquiv_ratio φ k (k.castSucc.succAbove j)).symm)
  apply RingHom.ext
  intro a
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (chartEquiv φ k a)
  change chartMap φ k p = chartEquiv φ k a at hp
  have h := RingHom.congr_fun he p
  change productEquiv φ i k (restrictOther φ i k ((chartEquiv φ k).symm (chartMap φ k p))) =
    overlapMap φ i k (chartMap φ k p) at h
  rw [hp, AlgEquiv.symm_apply_apply] at h
  exact h

/-- Restriction from the second projective chart is the weighted coordinate substitution
on every element of its affine coordinate ring. -/
theorem overlapSections_restrict_other (a : ChartRing φ k) :
    overlapSections φ i k (res (threefold φ).sheaf inf_le_right ((Proj.awayToSection (grade φ) _) a)) =
      overlapMap φ i k (chartEquiv φ k a) :=
  (readAt_other φ i k _ _ _ a).trans (RingHom.congr_fun (restrictOther_eq φ i k) a)

private theorem overlapChart_to_product :
    (overlapChart φ i k).inv ≫ (intersection φ i k).ι =
      Spec.map (CommRingCat.ofHom (productEquiv φ i k).toRingHom) ≫
        Proj.awayι (grade φ) (den φ i k) (den_mem φ i k) (by decide) := by
  simp only [overlapChart, Iso.trans_inv, Category.assoc, Scheme.isoOfEq_inv_ι,
    Proj.basicOpenIsoSpec_inv_ι]
  rfl

private theorem overlapChart_factor (j l : Fin 4) (hd : den φ i k = coord φ j.castSucc * coord φ l.castSucc)
    (f : chart φ j →+* overlap φ i k)
    (hf : (productEquiv φ i k).toRingHom.comp
        (HomogeneousLocalization.awayMap (grade φ) (weightOne_mem_grade φ l) hd) =
      f.comp (chartEquiv φ j).toRingEquiv.toRingHom) :
    (overlapChart φ i k).inv ≫ (intersection φ i k).ι =
      Spec.map (CommRingCat.ofHom f) ≫ (affineChart φ j).inv ≫ (coordinateOpen φ j).ι := by
  rw [overlapChart_to_product, ← Proj.SpecMap_awayMap_awayι (grade φ)
    (weightOne_mem_grade φ j) (by decide) (weightOne_mem_grade φ l) hd]
  have h : (affineChart φ j).inv ≫ (coordinateOpen φ j).ι =
      Spec.map (CommRingCat.ofHom (chartEquiv φ j).toRingEquiv.toRingHom) ≫
        Proj.awayι (grade φ) (coord φ j.castSucc) (weightOne_mem_grade φ j) (by decide) :=
    Category.assoc _ _ _
  rw [h]
  simp only [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun q : ChartRing φ j →+* overlap φ i k => Spec.map (CommRingCat.ofHom q) ≫
    Proj.awayι (grade φ) (coord φ j.castSucc) (weightOne_mem_grade φ j) (by decide)) hf

theorem overlapChart_to_first :
    (overlapChart φ i k).inv ≫ (intersection φ i k).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (chart φ i) (overlap φ i k))) ≫
        (affineChart φ i).inv ≫ (coordinateOpen φ i).ι :=
  overlapChart_factor φ i k i k rfl _ (RingHom.ext (productEquiv_restrict φ i k))

theorem overlapChart_to_second :
    (overlapChart φ i k).inv ≫ (intersection φ i k).ι =
      Spec.map (CommRingCat.ofHom (overlapMap φ i k).toRingHom) ≫
        (affineChart φ k).inv ≫ (coordinateOpen φ k).ι :=
  overlapChart_factor φ i k k i (mul_comm _ _) _ (restrictOther_eq φ i k)

theorem overlapChart_overBase :
    (overlapChart φ i k).inv ≫ (intersection φ i k).ι ≫ toBase φ =
      Spec.map (CommRingCat.ofHom (algebraMap R (overlap φ i k))) := by
  rw [← Category.assoc, overlapChart_to_first]
  simp only [Category.assoc, affineChart_overBase, ← Spec.map_comp]
  exact congrArg (fun q : R →+* overlap φ i k => Spec.map (CommRingCat.ofHom q))
    (IsScalarTower.algebraMap_eq R (chart φ i) (overlap φ i k)).symm

end CycleQ2HodgeEulerOverlapBinding
end

#print axioms CycleQ2HodgeEulerOverlapBinding.overlapChart
#print axioms CycleQ2HodgeEulerOverlapBinding.overlapSections_otherCoordinate

#print axioms CycleQ2HodgeEulerOverlapBinding.overlapChart_to_second
