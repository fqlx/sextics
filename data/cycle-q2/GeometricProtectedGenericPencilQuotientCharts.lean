import Proposal.GeometricProtectedGenericPencilProjMap
import Proposal.GeometricProtectedPencilDoubleCover
import Proposal.GeometricGradedAwaySpecialization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic.ComputeDegree

/-! On every standard affine chart of the protected generic pencil,
the projective double-cover map identifies the weighted chart ring with
the fixed ring of the paired sign. Clearing a power of the invariant
denominator produces a genuinely fixed homogeneous numerator. The trace-norm
quadratic and finite generation prove that the projective morphism is finite.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ProtectedGenericPencilQuotientCharts

open HomogeneousLocalization CycleQ2GradedAwaySpecialization

section Localization

variable {A B σ τ : Type} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

private def fraction (a x : A) (n : ℕ) : Localization.Away a :=
  Localization.mk x ⟨a^n, n, rfl⟩

private theorem fraction_eq (a x y : A) (n m : ℕ) :
    fraction a x n = fraction a y m ↔ ∃ k : ℕ, a^k * (a^m*x) = a^k * (a^n*y) := by
  rw [fraction, fraction, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  constructor
  · rintro ⟨⟨_,k,rfl⟩,h⟩
    exact ⟨k,h⟩
  · rintro ⟨k,h⟩
    exact ⟨⟨a^k,k,rfl⟩,h⟩

private theorem away_injective (f : 𝒜 →+*ᵍ ℬ) (h : Function.Injective f)
    {d : ℕ} (a : A) (ha : a ∈ 𝒜 d) : Function.Injective (Away.map f a) := by
  intro x y he
  obtain ⟨n,x,hx,rfl⟩ := Away.mk_surjective 𝒜 ha x
  obtain ⟨m,y,hy,rfl⟩ := Away.mk_surjective 𝒜 ha y
  rw [Away.map_mk, Away.map_mk] at he
  have he' : fraction (f a) (f x) n = fraction (f a) (f y) m := congrArg HomogeneousLocalization.val he
  obtain ⟨k,hk⟩ := (fraction_eq _ _ _ _ _).mp he'
  apply HomogeneousLocalization.val_injective
  apply (fraction_eq a x y n m).mpr
  exact ⟨k,h (by simpa only [map_mul, map_pow] using hk)⟩

private def fixedDenAction (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ ℬ) (h : ∀ x, g (f x) = f x) (a : A) :=
  awayMapOfEq g (f a) (f a) (h a)

private theorem away_fixed (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ ℬ) (h : ∀ x, g (f x) = f x)
    (hinj : Function.Injective f) (hlift : ∀ x, g x = x → ∃ y, f y = x)
    {d : ℕ} (a : A) (ha : a ∈ 𝒜 d) (x : Away ℬ (f a)) :
    fixedDenAction f g h a x = x ↔ ∃! y, Away.map f a y = x := by
  let b := f a
  have hb : b ∈ ℬ d := f.map_mem ha
  constructor
  · obtain ⟨n,x,hx,rfl⟩ := Away.mk_surjective ℬ hb x
    intro he
    rw [fixedDenAction, awayMapOfEq_mk g _ _ _ hb hb] at he
    have he' : fraction b (g x) n = fraction b x n := congrArg HomogeneousLocalization.val he
    obtain ⟨k,hk⟩ := (fraction_eq _ _ _ _ _).mp he'
    let l := k+n
    let t := b^l*x
    have ht : t ∈ ℬ ((l+n) • d) := by
      rw [add_smul]
      exact SetLike.mul_mem_graded (SetLike.pow_mem_graded l hb) hx
    have hgt : g t = t := by
      change g (b^l*x) = b^l*x
      rw [map_mul, map_pow, h a]
      simpa only [l,pow_add,mul_assoc] using hk
    obtain ⟨y,hy⟩ := hlift t hgt
    let u := DirectSum.decompose 𝒜 y ((l+n) • d)
    have hu : f (u : A) = t := by
      rw [show f (u : A) = (DirectSum.decompose ℬ (f y) ((l+n) • d) : B) from
        map_directSumDecompose 𝒜 ℬ f, hy]
      exact DirectSum.decompose_of_mem_same ℬ ht
    let z := Away.mk 𝒜 ha (l+n) (u : A) u.property
    have hz : Away.map f a z = Away.mk ℬ hb n x hx := by
      rw [show z = Away.mk 𝒜 ha (l+n) (u : A) u.property from rfl, Away.map_mk]
      apply HomogeneousLocalization.val_injective
      apply (fraction_eq b (f (u : A)) x (l+n) n).mpr
      exact ⟨0, by rw [hu]; simp [t, pow_add, mul_left_comm, mul_comm]⟩
    exact ⟨z,hz,fun w hw => away_injective f hinj a ha (hw.trans hz.symm)⟩
  · rintro ⟨y,rfl,_⟩
    obtain ⟨n,y,hy,rfl⟩ := Away.mk_surjective 𝒜 ha y
    rw [Away.map_mk, fixedDenAction, awayMapOfEq_mk g _ _ _ hb hb]
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, h y]
    rfl

end Localization

open MvPolynomial CycleQ2ProtectedGenericPencilModel CycleQ2ProtectedGenericPencilProjMap
open CycleQ2ProtectedPencilDoubleCover (beta sign coverMap coverMap_injective beta_coverMap beta_fixed_iff)

private theorem sign_homogeneous {k : Type} [Field k] {n : ℕ} {p : MvPolynomial (Fin 5) k}
    (hp : p.IsHomogeneous n) : (sign p).IsHomogeneous n := by
  let v : Fin 5 → MvPolynomial (Fin 5) k := ![X 0,X 1,X 2,X 3,-X 4]
  have hv (i : Fin 5) : (v i).IsHomogeneous 1 := by
    fin_cases i
    · exact isHomogeneous_X k 0
    · exact isHomogeneous_X k 1
    · exact isHomogeneous_X k 2
    · exact isHomogeneous_X k 3
    · exact (homogeneousSubmodule (Fin 5) k 1).neg_mem (isHomogeneous_X k 4)
  change (aeval v p).IsHomogeneous n
  simpa only [one_mul] using hp.aeval v hv

def betaGraded : ordinaryGrade →+*ᵍ ordinaryGrade where
  toRingHom := (beta G).toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact ⟨sign p, sign_homogeneous hp, rfl⟩

private theorem gradedCover_eq (y : QuotientRing) : gradedCover y = coverMap G y := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

private theorem cover_fixed (y : QuotientRing) : betaGraded (gradedCover y) = gradedCover y := by
  rw [gradedCover_eq]
  exact beta_coverMap G y

private theorem cover_injective : Function.Injective gradedCover := by
  intro y z h
  apply coverMap_injective G
  simpa only [gradedCover_eq] using h

def betaChart (a : QuotientRing) : Away ordinaryGrade (gradedCover a) →+* Away ordinaryGrade (gradedCover a) :=
  fixedDenAction gradedCover betaGraded cover_fixed a

theorem betaChart_fraction {d : ℕ} (a : QuotientRing) (ha : a ∈ grade d) (n : ℕ)
    (x : Ordinary) (hx : x ∈ ordinaryGrade (n • d)) :
    betaChart a (Away.mk ordinaryGrade (gradedCover.2 ha) n x hx) =
      Away.mk ordinaryGrade (gradedCover.2 ha) n (beta G x) (betaGraded.2 hx) :=
  awayMapOfEq_mk betaGraded _ _ (cover_fixed a) _ _ _ _ _

theorem coverChart_injective {d : ℕ} (a : QuotientRing) (ha : a ∈ grade d) :
    Function.Injective (Away.map gradedCover a) :=
  away_injective _ cover_injective _ ha

theorem betaChart_fixed_iff {d : ℕ} (a : QuotientRing) (ha : a ∈ grade d)
    (x : Away ordinaryGrade (gradedCover a)) :
    betaChart a x = x ↔ ∃! y, Away.map gradedCover a y = x := by
  apply away_fixed gradedCover betaGraded cover_fixed cover_injective _ a ha x
  intro b hb
  obtain ⟨y,hy,_⟩ := (beta_fixed_iff G b).mp hb
  exact ⟨y, (gradedCover_eq y).trans hy⟩

abbrev fixedChartRing (a : QuotientRing) := (betaChart a).eqLocus (RingHom.id _)

/-- Pullback to the ordinary chart is a ring isomorphism onto the equalizer
of its actual sign action and the identity. -/
def chartEquivFixed {d : ℕ} (a : QuotientRing) (ha : a ∈ grade d) :
    Away grade a ≃+* fixedChartRing a := by
  let f := (Away.map gradedCover a).codRestrict (fixedChartRing a) fun y =>
    (betaChart_fixed_iff a ha _).mpr ⟨y, rfl, fun w hw => coverChart_injective a ha hw⟩
  apply RingEquiv.ofBijective f
  constructor
  · intro x y h
    exact coverChart_injective a ha (congrArg Subtype.val h)
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,_⟩ := (betaChart_fixed_iff a ha x).mp hx
    exact ⟨y, Subtype.ext hy⟩

/-- On each member of the four-chart cover the pullback map of the actual
projective morphism has precisely the sign-invariant fractions as its image. -/
theorem patch_fixed_iff (i : Fin 4) (x : Away ordinaryGrade (gradedCover (quotient (X i.castSucc)))) :
    betaChart (quotient (X i.castSucc)) x = x ↔ ∃! y, Away.map gradedCover (quotient (X i.castSucc)) y = x :=
  betaChart_fixed_iff _ (degreeOneCoordinate i) x

private theorem beta_involutive_aux {k : Type} [Field k]
    (g : MvPolynomial (Fin 5) k) : Function.Involutive (beta g) := by
  have hi : (sign (K := k)).comp sign = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [sign]
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (CycleQ2ProtectedPencilDoubleCover.q (CycleQ2ProtectedPencilDoubleCover.square g))
    (AlgHom.congr_fun hi p)

theorem betaChart_involutive {d : ℕ} (a : QuotientRing) (ha : a ∈ grade d) :
    Function.Involutive (betaChart a) := by
  intro x
  obtain ⟨n,x,hx,rfl⟩ := Away.mk_surjective ordinaryGrade (gradedCover.2 ha) x
  rw [betaChart_fraction a ha, betaChart_fraction a ha]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, beta_involutive_aux G x]

/-- Every ordinary chart element satisfies its trace-norm quadratic over the
weighted chart, including at points of the branch divisor. -/
theorem coverChart_integral {d : ℕ} (a : QuotientRing) (ha : a ∈ grade d) :
    (Away.map gradedCover a).IsIntegral := by
  intro x
  have ht : betaChart a (x + betaChart a x) = x + betaChart a x := by
    rw [map_add, betaChart_involutive a ha x, add_comm]
  have hn : betaChart a (x * betaChart a x) = x * betaChart a x := by
    rw [map_mul, betaChart_involutive a ha x, mul_comm]
  obtain ⟨t,ht',_⟩ := (betaChart_fixed_iff a ha _).mp ht
  obtain ⟨n,hn',_⟩ := (betaChart_fixed_iff a ha _).mp hn
  refine ⟨Polynomial.X ^ 2 + (-Polynomial.C t * Polynomial.X + Polynomial.C n), ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_neg, ht', hn']
    ring

private theorem sign_degree_zero {k : Type} [Field k] (p : MvPolynomial (Fin 5) k)
    (hp : p.IsHomogeneous 0) : sign p = p := by
  obtain ⟨c,hc⟩ : ∃ c : k, p = C c :=
    ⟨_, totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 5)).mpr hp)⟩
  rw [hc]
  simp [sign]

private theorem cover_zero_fixed (x : Ordinary) (hx : x ∈ ordinaryGrade 0) :
    beta G x = x := by
  obtain ⟨p,hp,rfl⟩ := hx
  exact congrArg q (sign_degree_zero p hp)

private theorem chart_zero_fixed {d : ℕ} (a : QuotientRing) (ha : a ∈ grade d)
    (z : ordinaryGrade 0) :
    betaChart a (algebraMap (ordinaryGrade 0) (Away ordinaryGrade (gradedCover a)) z) =
      algebraMap (ordinaryGrade 0) (Away ordinaryGrade (gradedCover a)) z := by
  have hz : (z : Ordinary) ∈ ordinaryGrade (0 • d) := by
    rw [zero_smul]
    exact z.property
  have e : algebraMap (ordinaryGrade 0) (Away ordinaryGrade (gradedCover a)) z =
      Away.mk ordinaryGrade (gradedCover.2 ha) 0 (z : Ordinary) hz := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.algebraMap_eq, fromZeroRingHom, Away.val_mk]
  rw [e, betaChart_fraction a ha]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, cover_zero_fixed z z.property]

/-- Homogeneous localization of the protected cover is finite on every
basic affine with a homogeneous denominator. -/
theorem coverChart_finite {d : ℕ} (a : QuotientRing) (ha : a ∈ grade d) :
    (Away.map gradedCover a).Finite := by
  apply RingHom.finite_iff_isIntegral_and_finiteType.mpr
  refine ⟨coverChart_integral a ha, ?_⟩
  let c := (algebraMap (ordinaryGrade 0) (Away ordinaryGrade (gradedCover a))).codRestrict
    (fixedChartRing a) (chart_zero_fixed a ha)
  let k := (chartEquivFixed a ha).symm.toRingHom.comp c
  apply RingHom.FiniteType.of_comp_finiteType (f := k)
  have e : (Away.map gradedCover a).comp k =
      algebraMap (ordinaryGrade 0) (Away ordinaryGrade (gradedCover a)) := by
    apply RingHom.ext
    intro z
    exact congrArg Subtype.val ((chartEquivFixed a ha).apply_symm_apply (c z))
  rw [e, RingHom.finiteType_algebraMap]
  let : IsScalarTower K (ordinaryGrade 0) Ordinary :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := ordinaryGrade 0) (A := Ordinary) rfl
  let : Algebra.FiniteType (ordinaryGrade 0) Ordinary :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (ordinaryGrade 0) Ordinary
  exact Away.finiteType _ _ (gradedCover.2 ha)

open CategoryTheory AlgebraicGeometry

/-- The projective double cover is a finite morphism, including its branch locus. -/
theorem morphism_finite : IsFinite morphism := by
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ patch_cover).mpr
  intro i
  let a := quotient (X i.castSucc)
  let ha : a ∈ grade 1 := degreeOneCoordinate i
  let e := Proj.basicOpenIsoSpec grade a ha (by decide)
  let e' := Proj.basicOpenIsoSpec ordinaryGrade (gradedCover a) (gradedCover.2 ha) (by decide)
  let f := Spec.map (CommRingCat.ofHom (Away.map gradedCover a))
  have hc : e'.inv ≫ (morphism ∣_ patch i) = f ≫ e.inv := by
    apply (cancel_mono (patch i).ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
    exact (patch_affine i).trans (Category.assoc _ _ _).symm
  have h : (morphism ∣_ patch i) = e'.hom ≫ f ≫ e.inv := by
    rw [← hc, Iso.hom_inv_id_assoc]
  let : IsFinite f := (IsFinite.SpecMap_iff _).mpr (coverChart_finite a ha)
  rw [h]
  infer_instance

end CycleQ2ProtectedGenericPencilQuotientCharts
end

#print axioms CycleQ2ProtectedGenericPencilQuotientCharts.coverChart_injective
#print axioms CycleQ2ProtectedGenericPencilQuotientCharts.patch_fixed_iff
#print axioms CycleQ2ProtectedGenericPencilQuotientCharts.chartEquivFixed

#print axioms CycleQ2ProtectedGenericPencilQuotientCharts.coverChart_integral
#print axioms CycleQ2ProtectedGenericPencilQuotientCharts.morphism_finite
