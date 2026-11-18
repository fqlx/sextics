import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Regular sections on a dense open in a reduced affine Noetherian scheme

The complement ideal of the open has zero annihilator. In a Noetherian
ring this implies that the ideal contains a nonzero divisor. Restricting
to its principal open identifies every section with an element of the
total ring of fractions, also when the affine scheme is reducible.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2DenseOpenTotalFractions

open AlgebraicGeometry CategoryTheory Opposite PrimeSpectrum TopologicalSpace

variable (A : Type) [CommRing A] [IsReduced A] [IsNoetherianRing A]

/-- A dense open in a reduced Noetherian spectrum contains a principal open
cut out by a regular element. -/
theorem exists_regular_basicOpen (W : Opens (PrimeSpectrum A))
    (hW : Dense (W : Set (PrimeSpectrum A))) :
    ∃ s ∈ nonZeroDivisors A, basicOpen s ≤ W := by
  classical
  let I := vanishingIdeal (W : Set (PrimeSpectrum A))ᶜ
  have hI : zeroLocus (I : Set A) = (W : Set (PrimeSpectrum A))ᶜ :=
    (zeroLocus_vanishingIdeal_eq_closure _).trans W.isOpen.isClosed_compl.closure_eq
  have hV : vanishingIdeal (W : Set (PrimeSpectrum A)) = ⊥ := by
    rw [← vanishingIdeal_closure, hW.closure_eq, vanishingIdeal_univ, nilradical_eq_zero]
    rfl
  have hi : ((I : Set A) ∩ nonZeroDivisors A).Nonempty := by
    by_contra hn
    obtain ⟨x, hx, hne⟩ := (SetLike.lt_iff_le_and_exists.mp
      (Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors (I := I)
        (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hn)))).2
    apply hne
    rw [← hV, mem_vanishingIdeal]
    intro p hp
    have hnot : ¬ (I : Set A) ⊆ p.asIdeal := by
      intro h
      exact (hI ▸ (mem_zeroLocus p I).mpr h) hp
    obtain ⟨a, ha, hpa⟩ := Set.not_subset.mp hnot
    have hz : x * a = 0 := congrArg Subtype.val ((Module.mem_annihilator.mp hx) ⟨a, ha⟩)
    exact (p.isPrime.mem_or_mem (hz ▸ p.asIdeal.zero_mem)).resolve_right hpa
  obtain ⟨s, hsi, hs⟩ := hi
  refine ⟨s, hs, ?_⟩
  intro p hp
  by_contra hn
  have : p ∈ zeroLocus (I : Set A) := by rw [hI]; exact hn
  exact hp ((mem_zeroLocus _ _).mp this hsi)

omit [_root_.IsReduced A] [IsNoetherianRing A] in
private theorem dense_regular_basicOpen (s : A) (hs : s ∈ nonZeroDivisors A) :
    Dense (basicOpen s : Set (PrimeSpectrum A)) := by
  have hinj : Function.Injective (algebraMap A (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  rw [← localization_away_comap_range (Localization.Away s) s]
  apply (denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  exact bot_le

/-- Sections on the specified open, with their canonical algebra structure
over the ring of the ambient spectrum. -/
abbrev Sections (W : (Spec (CommRingCat.of A)).Opens) :=
  (Spec.structureSheaf A).obj.obj (op W)

/-- The dense principal-open restriction embeds sections in the total
quotient ring as an algebra over the original ring. -/
theorem sections_embedding (W : (Spec (CommRingCat.of A)).Opens)
    (hW : Dense (W : Set (Spec (CommRingCat.of A)))) :
    ∃ φ : Sections A W →ₐ[A] FractionRing A, Function.Injective φ := by
  obtain ⟨s, hs, hle⟩ := exists_regular_basicOpen A W hW
  let X := Spec (CommRingCat.of A)
  let D : X.Opens := basicOpen s
  have : IsDominant D.ι := ⟨by
    change Dense (Set.range D.ι)
    rw [Scheme.Opens.range_ι]
    exact dense_regular_basicOpen A s hs⟩
  have : IsSchemeTheoreticallyDominant D.ι := .of_isDominant _
  let res : Sections A W →ₐ[A] Sections A D :=
    { (X.presheaf.map (homOfLE hle).op).hom with
      commutes' := fun _ => rfl }
  have hinj : Function.Injective res := by
    intro z w h
    apply D.ι.app_injective W
    let i := homOfLE (D.ι_image_le (D.ι ⁻¹ᵁ W))
    have H := congrArg (X.presheaf.map i.op) h
    change (X.presheaf.map (homOfLE hle).op ≫ X.presheaf.map i.op) z =
      (X.presheaf.map (homOfLE hle).op ≫ X.presheaf.map i.op) w at H
    rw [← Functor.map_comp] at H
    exact H
  let incl : Sections A D →ₐ[A] FractionRing A :=
    IsLocalization.Away.liftAlgHom s (f := Algebra.ofId A (FractionRing A))
      (IsLocalization.map_units (FractionRing A) ⟨s, hs⟩)
  have hi : Function.Injective incl := by
    apply IsLocalization.injective_of_map_algebraMap_zero
      (M := Submonoid.powers s) (Sections A D) incl.toRingHom
    intro a ha
    have hzero : algebraMap A (FractionRing A) a = 0 :=
      (incl.commutes a).symm.trans ha
    have hz : a = 0 := IsFractionRing.injective A (FractionRing A)
      (hzero.trans (map_zero (algebraMap A (FractionRing A))).symm)
    simp [hz]
  exact ⟨incl.comp res, hi.comp hinj⟩

end CycleQ2DenseOpenTotalFractions
end

#print axioms CycleQ2DenseOpenTotalFractions.exists_regular_basicOpen
#print axioms CycleQ2DenseOpenTotalFractions.sections_embedding
