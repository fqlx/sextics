import Proposal.GeometricHodgeCyclicAction
import Proposal.GeometricHodgeEulerChartBinding

/-!
# Compatibility of the cyclic action with the actual affine charts

The substitution on normalized coordinates is the restriction of the weighted
projective automorphism. On a homogeneous fraction with denominator of power
n the inverse coordinate character contributes its n-th power.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicAction
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
  CycleQ2GeometricIncidenceProj CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
  CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient
  CycleQ2LiteralOrbitAction CycleQ2LiteralThreefoldOrbitAction CycleQ2SeedCyclicAction

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3 = 1) (i : Fin 4)

private theorem constant_mem (c : ℂ) : quotient φ (C c) ∈ grade φ 0 :=
  quotient_mem_grade φ _ (isWeightedHomogeneous_C _ _)

private theorem denominator_recovery :
    coord φ i.castSucc = gradedAction φ z hz (coord φ i.castSucc) * quotient φ (C (baseScale z i)) := by
  change quotient φ (X i.castSucc) = quotient φ (polynomialAction z (X i.castSucc)) * _
  have he : quotient φ (C (char z i.castSucc)) * quotient φ (C (baseScale z i)) = 1 := by
    rw [← (quotient φ).map_mul, ← C.map_mul, baseScale,
      mul_inv_cancel₀ (char_ne_zero z hz _), map_one, map_one]
  rw [action_X, map_mul, mul_right_comm, he, one_mul]

def awayAction : ChartRing φ i →+* ChartRing φ i :=
  (awayMap (grade φ) (constant_mem φ _) (denominator_recovery φ z hz i)).comp
    (Away.map (gradedAction φ z hz) (coord φ i.castSucc))

theorem chartEquiv_action (x : ChartRing φ i) :
    chartEquiv φ i (awayAction φ z hz i x) = chartAction φ z hz i (chartEquiv φ i x) := by
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective (grade φ) (weightOne_mem_grade φ i) x
  obtain ⟨p,hp,rfl⟩ := ha
  have hn : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  let b := baseScale z i
  let v := C (b^n) * polynomialAction z p
  have hv : v.IsWeightedHomogeneous geometricWeight n := by
    simpa only [zero_add] using (isWeightedHomogeneous_C geometricWeight (b^n)).mul
      (polynomialAction_weighted z hn)
  have hx : awayAction φ z hz i (fraction φ i n p hn) = fraction φ i n v hv := by
    apply HomogeneousLocalization.val_injective
    simp only [awayAction, RingHom.comp_apply, fraction, Away.map_mk, awayMap_mk, Away.val_mk]
    have he : gradedAction φ z hz (quotient φ p) * quotient φ (C b)^n = quotient φ v := by
      change quotient φ (polynomialAction z p) * quotient φ (C b)^n = quotient φ v
      simp only [v, map_mul, map_pow, mul_comm]
    rw [he]
  change chartEquiv φ i (awayAction φ z hz i (fraction φ i n p hn)) =
    chartAction φ z hz i (chartEquiv φ i (fraction φ i n p hn))
  rw [hx, chartEquiv_fraction, chartEquiv_fraction]
  change chartMap φ i (dehom i v) = chartMap φ i (chartPoly z i (dehom i p))
  rw [chartPoly_dehom z hz i p hn]
  simp only [v, b, map_mul, dehom, aeval_C, MvPolynomial.algebraMap_eq]

private theorem gradedAway_equivariant {A σ : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : 𝒜 →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (a : A) (ha : a ∈ 𝒜 1) (b : A) (hb : b ∈ 𝒜 0) (hab : a = f a * b) :
    Proj.awayι 𝒜 a ha (by decide) ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom ((awayMap 𝒜 hb hab).comp (Away.map f a))) ≫
        Proj.awayι 𝒜 a ha (by decide) := by
  let m := awayMap 𝒜 hb hab
  have he := Proj.SpecMap_awayMap_awayι 𝒜 (f.map_mem ha) (by decide) hb hab
  calc
    _ = (Spec.map (CommRingCat.ofHom m) ≫ Proj.awayι 𝒜 (f a) (f.map_mem ha) (by decide)) ≫
        Proj.map f hf := congrArg (fun g => g ≫ Proj.map f hf) he.symm
    _ = Spec.map (CommRingCat.ofHom m) ≫ Spec.map (CommRingCat.ofHom (Away.map f a)) ≫
        Proj.awayι 𝒜 a ha (by decide) := by
      rw [Category.assoc, Proj.awayι_comp_map]
    _ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl

set_option maxHeartbeats 800000 in
private theorem awayι_equivariant :
    Proj.awayι (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide) ≫ (action φ z hz).hom =
      Spec.map (CommRingCat.ofHom (awayAction φ z hz i)) ≫
        Proj.awayι (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide) :=
  gradedAway_equivariant (grade φ) (gradedAction φ z hz)
    (cyclic_irrelevant_le_map _ (gradedAction_cube φ z hz)) _
    (weightOne_mem_grade φ i) _ (constant_mem φ _) (denominator_recovery φ z hz i)

abbrev affineInclusion := (affineChart φ i).inv ≫ (coordinateOpen φ i).ι

private theorem affineInclusion_eq :
    affineInclusion φ i = Spec.map (CommRingCat.ofHom (chartEquiv φ i).toRingEquiv.toRingHom) ≫
      Proj.awayι (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide) := by
  change (Spec.map _ ≫ (coordinateChart φ i).inv) ≫ (coordinateOpen φ i).ι = _
  rw [Category.assoc]
  rfl

set_option maxHeartbeats 800000 in
theorem affineInclusion_equivariant :
    affineInclusion φ i ≫ (action φ z hz).hom =
      Spec.map (CommRingCat.ofHom (chartAction φ z hz i).toRingHom) ≫ affineInclusion φ i := by
  simp only [affineInclusion_eq]
  rw [Category.assoc, awayι_equivariant, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun p => Spec.map p ≫ Proj.awayι (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide))
  apply CommRingCat.hom_ext
  exact RingHom.ext (chartEquiv_action φ z hz i)

end CycleQ2HodgeCyclicAction
end

#print axioms CycleQ2HodgeCyclicAction.affineInclusion_equivariant
