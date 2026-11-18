import Proposal.GeometricAffineCohomology
import Proposal.GeometricCartierDerivedClass

/-!
# Local vanishing of positive sheaf cohomology on an affine spectrum

An injective presentation expresses any positive-degree class as a boundary.
Restriction commutes with this boundary. In degree one the section representing
the boundary lifts through the presentation on a finite principal cover.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2AffineCohomologyLocalVanishing

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2CechTwoToDerived

local notation "AffSheaf" => CycleQ2GeometricAffineCohomology.AbSheaf

local instance (A : Type) [CommRing A] : HasExt.{1} (AffSheaf A) :=
  HasExt.standard _

private theorem restrict_boundary {A : Type} [CommRing A] {S : ShortComplex (AffSheaf A)}
    (hS : S.ShortExact) {U V : Opens (PrimeSpectrum.Top A)} (h : U ≤ V)
    (n : ℕ) (y : S.X₃.H' n V) :
    (S.X₁.cohomologyPresheaf (n+1)).map (homOfLE h).op (Ext.comp y hS.extClass rfl) =
      Ext.comp ((S.X₃.cohomologyPresheaf n).map (homOfLE h).op y) hS.extClass rfl := by
  change (Ext.mk₀ (freeOpenMap h)).comp (Ext.comp y hS.extClass rfl) (zero_add _) =
    ((Ext.mk₀ (freeOpenMap h)).comp y (zero_add _)).comp hS.extClass rfl
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (zero_add (n + 1))).symm

private theorem exists_boundary (A : Type) [CommRing A] (F : AffSheaf A)
    (n : ℕ) (x : F.H' (n+1) ⊤) :
    ∃ y : (presentation F).X₃.H' n ⊤,
      Ext.comp y (presentation_shortExact F).extClass rfl = x :=
  Ext.covariant_sequence_exact₁ (freeOpen (X := PrimeSpectrum.Top A) ⊤) (presentation_shortExact F) x
    (Ext.eq_zero_of_injective _) (n₀ := n) rfl

/-- Every positive-degree derived cohomology class on an affine spectrum
vanishes after restriction to a finite family of distinguished opens which cover it. -/
theorem locally_zero (A : Type) [CommRing A] (F : AffSheaf A)
    (n : ℕ) (x : F.H' (n+1) ⊤) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ a ∈ s, (F.cohomologyPresheaf (n+1)).map (homOfLE
        (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op x = 0 := by
  classical
  induction n generalizing F with
  | zero =>
    let S := presentation F
    have hS := presentation_shortExact F
    obtain ⟨y, rfl⟩ := exists_boundary A F 0 x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    let : Sheaf.IsLocallySurjective S.g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr hS.epi_g
    obtain ⟨s, u, hs, hu⟩ := CycleQ2GeometricAffineCohomology.finite_local_lifts S.g
      (freeOpenSections S.X₃ ⊤ f)
    refine ⟨s, hs, ?_⟩
    intro a ha
    let U := PrimeSpectrum.basicOpen a
    let g := (freeOpenSections S.X₂ U).symm (u ⟨a, ha⟩)
    have hf : freeOpenMap (show U ≤ ⊤ from le_top) ≫ f = g ≫ S.g := by
      apply (freeOpenSections S.X₃ U).injective
      rw [freeOpenSections_naturality, ← freeOpenSections_postcomp]
      dsimp only [g]
      rw [AddEquiv.apply_symm_apply]
      exact (hu ⟨a, ha⟩).symm
    rw [restrict_boundary (A := A) hS (U := U) le_top 0 (Ext.mk₀ f)]
    change ((Ext.mk₀ (freeOpenMap (show U ≤ ⊤ from le_top))).comp
      (Ext.mk₀ f) (zero_add 0)).comp hS.extClass rfl = 0
    rw [Ext.mk₀_comp_mk₀, hf, ← Ext.mk₀_comp_mk₀_assoc]
    simp
  | succ n ih =>
    obtain ⟨y, rfl⟩ := exists_boundary A F (n+1) x
    obtain ⟨s, hs, hu⟩ := ih (presentation F).X₃ y
    refine ⟨s, hs, ?_⟩
    intro a ha
    rw [restrict_boundary (A := A) (presentation_shortExact F)
      (U := PrimeSpectrum.basicOpen a) le_top (n+1) y,
      hu a ha, Ext.zero_comp]

end CycleQ2AffineCohomologyLocalVanishing
end

#print axioms CycleQ2AffineCohomologyLocalVanishing.locally_zero
