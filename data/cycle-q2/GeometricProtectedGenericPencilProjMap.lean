/-
The basepoint-free Proj construction adapts Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor.
Copyright (c) 2026 Kenny Lau. All rights reserved. Released under Apache 2.0.
-/
import Proposal.GeometricProtectedGenericPencilModel
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# The Proj morphism of the protected generic double cover

A graded map gives a scheme morphism once homogeneous prime ideals contract to
relevant primes. The induced homomorphism on every basic affine is homogeneous
localization of that graded map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace CycleQ2ProtectedGenericPencilProjMap

namespace BasepointFree

section universe_polymorphic

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : ∀ p : ProjectiveSpectrum ℬ, ¬ 𝒜₊ ≤ p.1.comap f)


/-- Containment up to radical suffices for every relevant prime to contract to a relevant prime. -/
theorem relevant_of_radical (H : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f).radical)
    (p : ProjectiveSpectrum ℬ) : ¬ 𝒜₊ ≤ p.1.comap f := by
  intro hp
  apply p.3
  exact toIdeal_le_toIdeal_iff.mp (H.trans (p.2.isRadical.radical_le_iff.mpr
    (Ideal.map_le_of_le_comap (show 𝒜₊.toIdeal ≤ p.1.toIdeal.comap f from hp))))

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
@[simps] def pointMap (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le := hf p

/-- The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
def baseMap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := pointMap f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩



open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ baseMap f hf ⁻¹' U.1)

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def sectionValue
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨baseMap f hf y.1, hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
lemma isLocallyFraction_sectionValue
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (sectionValue f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨baseMap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (baseMap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [sectionValue]

set_option backward.isDefEq.respectTransparency false in
/-- The underlying ring hom of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def sectionMap :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨sectionValue _ _ _ _ hUV s.1,
      isLocallyFraction_sectionValue _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [sectionValue]
  map_zero' := by ext; simp [sectionValue]
  map_add' x y := by ext; simp [sectionValue]
  map_mul' x y := by ext; simp [sectionValue]


end universe_polymorphic

section universe_monomorphic


variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : ∀ p : ProjectiveSpectrum ℬ, ¬ 𝒜₊ ≤ p.1.comap f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces. -/
@[simps! (isSimp := false)] noncomputable def spaceMap :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| baseMap f hf
      c := { app U := CommRingCat.ofHom <| sectionMap f hf _ _ Set.Subset.rfl } }

set_option backward.isDefEq.respectTransparency.types false in
lemma germ_fraction {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (baseMap f hf p).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (spaceMap f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((spaceMap f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise] theorem map_stalk (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (baseMap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (spaceMap f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_fraction]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of `Proj`. -/
noncomputable def map : Proj ℬ ⟶ Proj 𝒜 where
  __ := (spaceMap f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← map_stalk] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜 (baseMap f hf p)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem preimage_basicOpen (s : A) :
    map f hf ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 s = AlgebraicGeometry.Proj.basicOpen ℬ (f s) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem map_open (s : A) : (AlgebraicGeometry.Proj.basicOpen ℬ (f s)).ι ≫ map f hf =
    (map f hf).resLE _ _ le_rfl ≫ (AlgebraicGeometry.Proj.basicOpen 𝒜 s).ι := by simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] lemma map_awaySections {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 s ≫
      Scheme.Hom.appLE (map f hf) (AlgebraicGeometry.Proj.basicOpen 𝒜 s) (AlgebraicGeometry.Proj.basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) ≫
      AlgebraicGeometry.Proj.awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The following square commutes:
```
Proj ℬ         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
@[reassoc] theorem map_awayChart {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    awayι ℬ (f s) (f.2 hs) hi ≫ map f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi := by
  rw [awayι, awayι, Category.assoc, map_open, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (AlgebraicGeometry.Proj.basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, map_awaySections _ _ hs]

end universe_monomorphic
end BasepointFree

section Pencil
noncomputable section
open MvPolynomial CycleQ2ProtectedGenericPencilModel CycleQ2IncidenceNormalForm
  CycleQ2GeometricIncidenceProj CycleQ2GeometricProjectiveCurve.HomogeneousQuotient

attribute [local instance] MvPolynomial.gradedAlgebra

private def values : Fin 5 → P := ![X 0, X 1, X 2, X 3, X 4 ^ 2]

private theorem values_homogeneous (i : Fin 5) :
    (values i).IsHomogeneous (geometricWeight i) := by
  fin_cases i
  · exact isHomogeneous_X K 0
  · exact isHomogeneous_X K 1
  · exact isHomogeneous_X K 2
  · exact isHomogeneous_X K 3
  · exact isHomogeneous_X_pow (4 : Fin 5) 2

theorem square_homogeneous {d : ℕ} {p : P} (hp : p.IsWeightedHomogeneous geometricWeight d) :
    (square p).IsHomogeneous d := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using isHomogeneous_zero (Fin 5) K d
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial e c he =>
    rw [square, aeval_monomial]
    change (C c * ∏ i ∈ e.support, values i ^ e i).IsHomogeneous d
    have hprod := (IsHomogeneous.prod e.support (fun i => values i ^ e i)
      (fun i => geometricWeight i * e i) (fun i _ => (values_homogeneous i).pow (e i))).C_mul c
    have hd : (∑ i ∈ e.support, geometricWeight i * e i) = d := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using he
    exact hd ▸ hprod

abbrev Ordinary := P ⧸ Ideal.span {square G}
abbrev q := Ideal.Quotient.mkₐ K (Ideal.span {square G} : Ideal P)
abbrev ordinaryPolynomialGrade := homogeneousSubmodule (Fin 5) K
abbrev ordinaryGrade (n : ℕ) : Submodule K Ordinary :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    ordinaryPolynomialGrade (Ideal.span {square G}) n

instance : GradedRing ordinaryGrade :=
  gradedRing ordinaryPolynomialGrade (Ideal.span {square G}) (by
    apply Ideal.homogeneous_span
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact ⟨6, square_homogeneous G_homogeneous⟩)

/-- The ordinary projective sextic on the generic pencil hyperplane. -/
def ordinaryPencil : Scheme := Proj ordinaryGrade

theorem ordinary_defining_ideal :
    Ideal.span ({square G} : Set P) = Ideal.span {restrictProtected HodgeSubmission.F} :=
  congrArg (fun p : P => Ideal.span ({p} : Set P)) restrictProtected_F.symm

/-- The graded homomorphism of the double cover sends w to u². -/
def gradedCover : CycleQ2ProtectedGenericPencilModel.grade →+*ᵍ ordinaryGrade where
  toRingHom := (Ideal.quotientMapₐ (Ideal.span {square G}) square (by
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact Ideal.subset_span (Set.mem_singleton _))).toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact ⟨square p, square_homogeneous hp, rfl⟩

theorem gradedCover_quotient (p : P) : gradedCover (quotient p) = q (square p) := rfl

private theorem coordinates_mem_irrelevant (i : Fin 5) :
    quotient (X i) ∈ HomogeneousIdeal.irrelevant CycleQ2ProtectedGenericPencilModel.grade :=
  HomogeneousIdeal.mem_irrelevant_of_mem _
    (CycleQ2IncidenceFamilyContainment.geometricWeight_pos i)
    ⟨X i, isWeightedHomogeneous_X K geometricWeight i, rfl⟩

private theorem positivePolynomial_mem (n : ℕ) (hn : 0 < n) (p : P) (hp : p.IsHomogeneous n) :
    p ∈ Ideal.span (Set.range (X : Fin 5 → P)) := by
  rw [← Set.image_univ]
  apply mem_ideal_span_X_image.mpr
  intro e he
  have he0 : e ≠ 0 := by
    intro h
    have hd := hp (mem_support_iff.mp he)
    simp only [h, map_zero] at hd
    omega
  obtain ⟨i,hi⟩ : ∃ i : Fin 5, e i ≠ 0 := by
    by_contra! h
    apply he0
    ext i
    exact h i
  exact ⟨i, Set.mem_univ i, hi⟩

theorem relevant (p : ProjectiveSpectrum ordinaryGrade) :
    ¬ HomogeneousIdeal.irrelevant CycleQ2ProtectedGenericPencilModel.grade ≤ p.1.comap gradedCover := by
  intro h
  have all (i : Fin 5) : gradedCover (quotient (X i)) ∈ p.1.toIdeal := h (coordinates_mem_irrelevant i)
  have hvars : Ideal.span (Set.range (X : Fin 5 → P)) ≤ p.1.toIdeal.comap q := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change q (X i) ∈ p.1.toIdeal
    have he := all i
    change q (square (X i)) ∈ p.1.toIdeal at he
    change q ((aeval values : P →ₐ[K] P) (X i)) ∈ p.1.toIdeal at he
    rw [aeval_X] at he
    fin_cases i
    · exact he
    · exact he
    · exact he
    · exact he
    · change q (X 4 ^ 2) ∈ p.1.toIdeal at he
      rw [map_pow] at he
      exact p.2.mem_of_pow_mem 2 he
  apply p.3
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn x hx
  obtain ⟨a,ha,rfl⟩ := hx
  exact hvars (positivePolynomial_mem n hn a ha)

/-- The projective morphism induced by squaring the fifth pencil coordinate. -/
def morphism : ordinaryPencil ⟶ hypersurface := BasepointFree.map gradedCover relevant

theorem morphism_point (p : ordinaryPencil) :
    (morphism p).asHomogeneousIdeal = p.asHomogeneousIdeal.comap gradedCover := rfl

theorem morphism_preimage (a : QuotientRing) : morphism ⁻¹ᵁ Proj.basicOpen _ a =
    Proj.basicOpen ordinaryGrade (gradedCover a) := rfl

theorem morphism_affine {d : ℕ} (hd : 0 < d) (a : QuotientRing)
    (ha : a ∈ CycleQ2ProtectedGenericPencilModel.grade d) :
    Proj.awayι ordinaryGrade (gradedCover a) (gradedCover.2 ha) hd ≫ morphism =
      Spec.map (CommRingCat.ofHom (Away.map gradedCover a)) ≫
        Proj.awayι CycleQ2ProtectedGenericPencilModel.grade a ha hd :=
  BasepointFree.map_awayChart gradedCover relevant hd a ha

theorem degreeOneCoordinate (i : Fin 4) :
    quotient (X i.castSucc) ∈ CycleQ2ProtectedGenericPencilModel.grade 1 := by
  refine ⟨X i.castSucc, ?_, rfl⟩
  have h : geometricWeight i.castSucc = 1 := by fin_cases i <;> rfl
  exact h ▸ isWeightedHomogeneous_X K geometricWeight i.castSucc

theorem gradedCover_coordinate (i : Fin 4) :
    gradedCover (quotient (X i.castSucc)) = q (X i.castSucc) := by
  rw [gradedCover_quotient]
  change q ((aeval values : P →ₐ[K] P) (X i.castSucc)) = _
  rw [aeval_X]
  fin_cases i <;> rfl

theorem preimage_patch (i : Fin 4) : morphism ⁻¹ᵁ patch i =
    AlgebraicGeometry.Proj.basicOpen ordinaryGrade (q (X i.castSucc)) := by
  rw [patch, morphism_preimage, gradedCover_coordinate]

/-- On each of the four weight-one patches, pullback is the map on
homogeneous fractions induced by the original square substitution. -/
theorem patch_affine (i : Fin 4) :
    Proj.awayι ordinaryGrade (gradedCover (quotient (X i.castSucc)))
        (gradedCover.2 (degreeOneCoordinate i)) (by decide) ≫ morphism =
      Spec.map (CommRingCat.ofHom (Away.map gradedCover (quotient (X i.castSucc)))) ≫
        Proj.awayι CycleQ2ProtectedGenericPencilModel.grade (quotient (X i.castSucc))
          (degreeOneCoordinate i) (by decide) :=
  morphism_affine (by decide) _ (degreeOneCoordinate i)

end
end Pencil

end CycleQ2ProtectedGenericPencilProjMap

#print axioms CycleQ2ProtectedGenericPencilProjMap.BasepointFree.map_awayChart

#print axioms CycleQ2ProtectedGenericPencilProjMap.morphism_affine
