import Proposal.GeometricIncidenceProperNeighborhood
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Extending smoothness from the generic fiber of a proper morphism

Flat preimmersions induce isomorphisms on stalks. A smooth pullback along
such a map therefore identifies points of the original smooth locus. For
a proper morphism, the image of the complement of this locus is closed.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ProperGenericSmoothNeighborhood

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CycleQ2IncidenceProperNeighborhood
open scoped nonZeroDivisors

universe u
variable {X Y T : Scheme.{u}}

/-- A flat preimmersion induces local ring isomorphisms on its image. -/
theorem isIso_stalkMap_of_flat_preimmersion (f : X ⟶ Y) [Flat f] [IsPreimmersion f]
    (x : X) : IsIso (f.stalkMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, f.stalkMap_surjective x⟩
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

/-- Smoothness of the pullback gives smoothness of the original stalk maps
at every point in the image of the pullback. -/
theorem pullback_point_mem_smoothLocus (g : T ⟶ Y) [Flat g] [IsPreimmersion g]
    (p : X ⟶ Y) [LocallyOfFinitePresentation p] (hs : Smooth (pullback.fst g p))
    (z : (pullback g p : Scheme.{u})) : pullback.snd g p z ∈ p.smoothLocus := by
  let a := pullback.fst g p
  let b := pullback.snd g p
  have : IsIso (g.stalkMap (a z)) := isIso_stalkMap_of_flat_preimmersion g _
  have : IsIso (b.stalkMap z) := isIso_stalkMap_of_flat_preimmersion b _
  have ha : (a.stalkMap z).hom.FormallySmooth := by
    change z ∈ a.smoothLocus
    rw [a.smoothLocus_eq_top]
    trivial
  have hcomp : ((a ≫ g).stalkMap z).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.FormallySmooth.respectsIso.cancel_left_isIso]
    exact ha
  have hpb : a ≫ g = b ≫ p := pullback.condition
  rw [hpb, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.FormallySmooth.respectsIso.cancel_right_isIso] at hcomp
  exact hcomp

/-- Smoothness along a whole fiber of a proper morphism extends over a base open. -/
theorem exists_smooth_neighborhood_of_preimmersion (g : T ⟶ Y) [Flat g] [IsPreimmersion g]
    (p : X ⟶ Y) [IsProper p] [LocallyOfFinitePresentation p]
    (hs : Smooth (pullback.fst g p)) (t : T) :
    ∃ V : Y.Opens, g t ∈ V ∧ Smooth (p ∣_ V) := by
  let V := properBaseNeighborhood p p.smoothLocus
  have ht : g t ∈ V := by
    apply (mem_properBaseNeighborhood_iff p p.smoothLocus (g t)).mpr
    intro x hx
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := p) t x hx.symm
    simpa only [← hz] using pullback_point_mem_smoothLocus g p hs z
  refine ⟨V, ht, ?_⟩
  have hsource : Smooth ((p ⁻¹ᵁ V).ι ≫ p) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq, ← top_le_iff]
    intro x _
    exact properBaseNeighborhood_preimage_le p p.smoothLocus x.2
  apply MorphismProperty.of_postcomp (W' := @IsOpenImmersion) @Smooth (p ∣_ V) V.ι inferInstance
  simpa only [morphismRestrict_ι] using hsource

abbrev genericMorphism (R : Type u) [CommRing R] [IsDomain R] :
    Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))

/-- A proper finitely presented family with smooth generic fiber is smooth
over an open neighborhood of the generic point of its integral affine base. -/
theorem exists_smooth_neighborhood {R : Type u} [CommRing R] [IsDomain R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] [LocallyOfFinitePresentation p]
    (hs : Smooth (pullback.fst (genericMorphism R) p)) :
    ∃ V : (Spec (CommRingCat.of R)).Opens,
      genericMorphism R (default : Spec (CommRingCat.of (FractionRing R))) ∈ V ∧ Smooth (p ∣_ V) := by
  have : Flat (genericMorphism R) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : IsPreimmersion (genericMorphism R) := IsPreimmersion.of_isLocalization (S := FractionRing R) R⁰
  exact exists_smooth_neighborhood_of_preimmersion (genericMorphism R) p hs default

end CycleQ2ProperGenericSmoothNeighborhood

#print axioms CycleQ2ProperGenericSmoothNeighborhood.exists_smooth_neighborhood_of_preimmersion
#print axioms CycleQ2ProperGenericSmoothNeighborhood.exists_smooth_neighborhood
