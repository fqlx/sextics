import Proposal.GeometricHodgeNormalExact
import Proposal.GeometricOpenCoverAdditiveExactness
import Proposal.GeometricCanonicalCechBoundary
import Proposal.GeometricCartierDeformation
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# The projective normal connecting homomorphism

For the genuine normal morphism on the smooth moving hypersurface, a
section of O(6) gives an ordinary derived degree-one class of its kernel.
Its kernel consists precisely of globally lifted coordinate velocities.
If the five twist groups in degree one vanish, every deformation class
of that kernel arises from a global section of the normal line.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeNormalCohomology

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Abelian
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
open CycleQ2GeometricOpenCoverAdditiveExactness (additiveComplex)
open CycleQ2GeometricConeCech.HZero (sectionsEquiv)
open CycleQ2GeometricCanonicalCechBoundary (sectionsEquiv_map)
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2GenericSexticGradient (CoeffRing)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
local instance (T : TopCat.{0}) : HasExt.{1} (AbSheaf T) := HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

abbrev Add (M : (threefold φ).Modules) :=
  (SheafOfModules.toSheaf (threefold φ).ringCatSheaf).obj M
abbrev H (M : (threefold φ).Modules) (n : ℕ) := Sheaf.H'.{1} (Add φ M) n ⊤

abbrev addNormal := additiveComplex (normalSequence φ)

theorem addNormal_exact (hg : IsUnit (φ goodParameter)) : (addNormal φ).ShortExact := by
  let F := SheafOfModules.toSheaf (threefold φ).ringCatSheaf
  have hS := normalSequence_exact φ hg
  have h := hS.exact.map_of_mono_of_preservesKernel F hS.mono_f inferInstance
  refine { exact := h, mono_f := ?_, epi_g := ?_ }
  · change Mono (F.map (kernel.ι (normalMap φ)))
    infer_instance
  · exact normal_additive_epi φ hg

def connecting (hg : IsUnit (φ goodParameter)) : Γ(twist φ 6,⊤) →+ H φ (rawTangent φ) 1 :=
  (CycleQ2GeometricIntrinsicCartierCohomology.openConnecting (addNormal_exact φ hg) 0 ⊤).comp
    (sectionsEquiv (addNormal φ).X₃ ⊤).symm.toAddMonoidHom

theorem connecting_zero_iff (hg : IsUnit (φ goodParameter)) (s : Γ(twist φ 6,⊤)) :
    connecting φ hg s = 0 ↔ ∃ a : Γ(raw φ,⊤), (normalMap φ).app ⊤ a = s := by
  let S := addNormal φ
  let z := (sectionsEquiv S.X₃ ⊤).symm s
  have hnat (a : S.X₂.H' 0 ⊤) :
      sectionsEquiv S.X₃ ⊤ (a.comp (Ext.mk₀ S.g) (add_zero 0)) =
        (normalMap φ).app ⊤ (sectionsEquiv S.X₂ ⊤ a) := sectionsEquiv_map S.g ⊤ a
  constructor
  · intro hs
    obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (freeOpen (⊤ : (threefold φ).Opens))
      (addNormal_exact φ hg) z rfl hs
    refine ⟨sectionsEquiv S.X₂ ⊤ a, (hnat a).symm.trans ?_⟩
    rw [ha]
    exact AddEquiv.apply_symm_apply _ _
  · rintro ⟨a,ha⟩
    let b := (sectionsEquiv S.X₂ ⊤).symm a
    have hb : b.comp (Ext.mk₀ S.g) (add_zero 0) = z := by
      apply (sectionsEquiv S.X₃ ⊤).injective
      rw [hnat]
      simpa only [b, z, AddEquiv.apply_symm_apply] using ha
    change z.comp (addNormal_exact φ hg).extClass rfl = 0
    rw [← hb, Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

def rawHEquiv (n : ℕ) : H φ (raw φ) n ≃+ (∀ j, H φ (pieces φ j) n) := by
  let F := SheafOfModules.toSheaf (threefold φ).ringCatSheaf
  let Z := fun j => F.obj (pieces φ j)
  let A := freeOpen (⊤ : (threefold φ).Opens)
  let e := PreservesProduct.iso F (pieces φ) ≪≫ (biproduct.isoProduct Z).symm
  exact (((extFunctorObj A n).mapIso e).addCommGroupIsoToAddEquiv).trans
    (Ext.addEquivBiproduct A (biproduct.isBilimit Z) n)

theorem connecting_surjective (hg : IsUnit (φ goodParameter))
    (hv : ∀ j, Subsingleton (H φ (pieces φ j) 1)) : Function.Surjective (connecting φ hg) := by
  intro c
  have hraw : Subsingleton (H φ (raw φ) 1) := by
    letI j := hv j
    exact (rawHEquiv φ 1).injective.subsingleton
  obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₁ (freeOpen (⊤ : (threefold φ).Opens)) (addNormal_exact φ hg)
    c (hraw.elim _ _) rfl
  refine ⟨sectionsEquiv (addNormal φ).X₃ ⊤ b, ?_⟩
  change ((sectionsEquiv _ _).symm ((sectionsEquiv _ _) b)).comp _ _ = _
  rwa [AddEquiv.symm_apply_apply]

end CycleQ2HodgeNormalCohomology
end

#print axioms CycleQ2HodgeNormalCohomology.connecting_zero_iff
#print axioms CycleQ2HodgeNormalCohomology.connecting_surjective
