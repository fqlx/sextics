import Proposal.GeometricNormalCurveSmooth
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth generic fibers of normal curve charts

The generic fiber of an affine normal domain over an integral coefficient
ring is its localization at the nonzero coefficients. When this fiber has
dimension at most one and the coefficient function field is perfect, it is
smooth even at boundary points of a model.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2NormalGenericChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors

variable {R A : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [IsIntegrallyClosed A]

abbrev GenericRing (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] :=
  FractionRing R ⊗[R] A

omit [IsIntegrallyClosed A] [IsDomain R] in
private theorem regular_coefficients (hi : Function.Injective (algebraMap R A)) :
    Algebra.algebraMapSubmonoid A R⁰ ≤ A⁰ := by
  exact Submonoid.map_le_iff_le_comap.mpr
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hi)

omit [IsIntegrallyClosed A] in
theorem generic_domain (hi : Function.Injective (algebraMap R A)) : IsDomain (GenericRing R A) := by
  let _ : Algebra A (GenericRing R A) := Algebra.TensorProduct.rightAlgebra
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _ (regular_coefficients hi)

/-- The actual generic coordinate algebra remains an integrally closed domain. -/
theorem generic_normal (hi : Function.Injective (algebraMap R A)) :
    IsDomain (GenericRing R A) ∧ IsIntegrallyClosed (GenericRing R A) := by
  let _ : Algebra A (GenericRing R A) := Algebra.TensorProduct.rightAlgebra
  exact ⟨generic_domain hi,
    isIntegrallyClosed_of_isLocalization _ _ (regular_coefficients hi)⟩

/-- A normal affine chart with one-dimensional generic fiber has a smooth generic fiber. -/
theorem generic_smooth [PerfectField (FractionRing R)] [Algebra.FiniteType R A]
    (hi : Function.Injective (algebraMap R A)) [Ring.KrullDimLE 1 (GenericRing R A)] :
    Algebra.Smooth (FractionRing R) (GenericRing R A) := by
  obtain ⟨hd, hn⟩ := generic_normal hi
  exact CycleQ2NormalCurveSmooth.smooth_of_normal_affine_curve (FractionRing R) (GenericRing R A)

abbrev genericMorphism (R : Type) [CommRing R] [IsDomain R] :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))

theorem smooth_affine_of_generic_algebra {S : Type} [CommRing S] [Algebra R S]
    (hs : Algebra.Smooth (FractionRing R) (GenericRing R S)) :
    Smooth (pullback.fst (genericMorphism R) (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := by
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
    (pullbackSpecIso R (FractionRing R) S).inv _).mp
  rw [pullbackSpecIso_inv_fst]
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr hs

/-- The affine criterion applies to the literal scheme-theoretic generic fiber. -/
theorem smooth_affine_generic_fiber [PerfectField (FractionRing R)] [Algebra.FiniteType R A]
    (hi : Function.Injective (algebraMap R A)) [Ring.KrullDimLE 1 (GenericRing R A)] :
    Smooth (pullback.fst (genericMorphism R) (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
  smooth_affine_of_generic_algebra (generic_smooth hi)

private theorem dimension_of_affine_immersion {F : Scheme} {T : Type} [CommRing T]
    (a : Spec (CommRingCat.of T) ⟶ F) [IsOpenImmersion a]
    (hd : ∀ W : F.affineOpens, Ring.KrullDimLE 1 Γ(F, W.1)) : Ring.KrullDimLE 1 T := by
  have hU := isAffineOpen_opensRange a
  let e := a.isoOpensRange ≪≫ hU.isoSpec
  have h := Ring.krullDimLE_iff.mp (hd ⟨a.opensRange, hU⟩)
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  apply Ring.krullDimLE_iff.mpr
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).le.trans h

omit [IsIntegrallyClosed A] [IsDomain A] in
/-- Dimension on affine charts of the generic fiber controls base change of a total affine chart. -/
theorem generic_patch_dimension {X : Scheme} (p : X ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hd : ∀ W : (pullback (genericMorphism R) p).affineOpens,
      Ring.KrullDimLE 1 Γ(pullback (genericMorphism R) p, W.1)) :
    Ring.KrullDimLE 1 (GenericRing R A) := by
  let g := genericMorphism R
  let a : Spec (CommRingCat.of (GenericRing R A)) ⟶ pullback g p :=
    (pullbackSpecIso R (FractionRing R) A).inv ≫
      (pullback.congrHom (rfl : g = g) hj).inv ≫
        (pullbackLeftPullbackSndIso g p j).inv ≫ pullback.fst _ _
  have : IsOpenImmersion a := by dsimp only [a]; infer_instance
  exact dimension_of_affine_immersion a hd

/-- The dimension hypothesis can be read on the original generic fiber, even for a
chart meeting the boundary of a compactification. -/
theorem smooth_normal_patch [PerfectField (FractionRing R)] [Algebra.FiniteType R A]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hi : Function.Injective (algebraMap R A))
    (hd : ∀ W : (pullback (genericMorphism R) p).affineOpens,
      Ring.KrullDimLE 1 Γ(pullback (genericMorphism R) p, W.1)) :
    Smooth (pullback.fst (genericMorphism R) (j ≫ p)) := by
  have := generic_patch_dimension p j hj hd
  rw [hj]
  exact smooth_affine_generic_fiber hi

/-- Smoothness on the generic fibers of the affine charts gives smoothness of the
whole generic fiber of the given morphism. -/
theorem smooth_generic_of_cover {X : Scheme} (p : X ⟶ Spec (CommRingCat.of R))
    (C : X.OpenCover) (h : ∀ i, Smooth (pullback.fst (genericMorphism R) (C.f i ≫ p))) :
    Smooth (pullback.fst (genericMorphism R) p) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth)
    (C.pullback₁ (pullback.snd (genericMorphism R) p))).mpr
  change ∀ i : C.I₀, Smooth (pullback.fst (pullback.snd (genericMorphism R) p) (C.f i) ≫
    pullback.fst (genericMorphism R) p)
  intro i
  rw [← pullbackLeftPullbackSndIso_hom_fst]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
    (pullbackLeftPullbackSndIso (genericMorphism R) p (C.f i)).hom _).mpr (h i)

end CycleQ2NormalGenericChart
end

#print axioms CycleQ2NormalGenericChart.smooth_affine_generic_fiber
#print axioms CycleQ2NormalGenericChart.smooth_normal_patch
#print axioms CycleQ2NormalGenericChart.smooth_generic_of_cover
