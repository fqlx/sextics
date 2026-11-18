import Proposal.GeometricLiteralResidueExactness

/-!
# From a class supported on a proper closed subset to a rational primitive

For an additive sheaf on a closed subspace, its direct image has only the
zero section on an open disjoint from the subspace. Consequently any
section in the sheaf image of a morphism out of this direct image restricts
to zero on the whole open complement. Applied to the protected residue,
this gives its rational primitive from a representative supported on a
proper closed subset.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueClosedSupport

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open CycleQ2GeometricAffineCohomology CycleQ2LiteralResidueLocalImage
open CycleQ2LiteralResidueSheaf CycleQ2LiteralResidueExactness
open CycleQ2GeometricRegularDeRham CycleQ2AffineClearing

variable {A : Type} [CommRing A]

def closedInclusion (Z : Closeds (PrimeSpectrum.Top A)) : TopCat.of Z ⟶ PrimeSpectrum.Top A :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

abbrev directImage (Z : Closeds (PrimeSpectrum.Top A))
    (K : (TopCat.of Z).Sheaf AddCommGrpCat.{0}) : AbSheaf A :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (closedInclusion Z)).obj K

/-- The inverse image of such an open is empty, so its section group is terminal. -/
theorem sections_subsingleton_off (Z : Closeds (PrimeSpectrum.Top A))
    (K : (TopCat.of Z).Sheaf AddCommGrpCat.{0}) (U : Opens (PrimeSpectrum.Top A))
    (hU : U ≤ Z.compl) : Subsingleton ((directImage Z K).obj.obj (op U)) := by
  have hempty : (Opens.map (closedInclusion Z)).obj U = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    exact False.elim ((hU hz) z.property)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (K.isTerminalOfEqEmpty hempty).isZero

/-- Sheaf-image membership suffices. Local sections of the direct image giving the
lifts restrict into the zero group everywhere on the complement. -/
theorem restrict_eq_zero_of_mem_image (Z : Closeds (PrimeSpectrum.Top A))
    (K : (TopCat.of Z).Sheaf AddCommGrpCat.{0}) {G : AbSheaf A} (f : directImage Z K ⟶ G)
    (ω : G.obj.obj (op ⊤)) (hω : (cokernel.π f).hom.app (op ⊤) ω = 0) :
    G.obj.map (homOfLE (show Z.compl ≤ ⊤ from le_top)).op ω = 0 := by
  let i : Z.compl ⟶ ⊤ := homOfLE le_top
  let u := G.obj.map i.op ω
  have hu : (cokernel.π f).hom.app (op Z.compl) u = 0 := by
    change (cokernel.π f).hom.app (op Z.compl) (G.obj.map i.op ω) = 0
    rw [NatTrans.naturality_apply, hω, map_zero]
  change u = 0
  apply TopCat.Presheaf.IsSheaf.section_ext G.property
  intro x hx
  obtain ⟨s, h, hxs, w, hw⟩ := exists_principal_preimage f Z.compl u hu x hx
  have := sections_subsingleton_off Z K (PrimeSpectrum.basicOpen s) h
  refine ⟨PrimeSpectrum.basicOpen s, h, hxs, ?_⟩
  change G.obj.map (homOfLE h).op u = G.obj.map (homOfLE h).op 0
  rw [← hw, Subsingleton.elim w 0, map_zero, map_zero]

private theorem image_section_cokernel {F G : AbSheaf A} (f : F ⟶ G)
    (v : (image f).obj.obj (op ⊤)) :
    (cokernel.π f).hom.app (op ⊤) ((image.ι f).hom.app (op ⊤) v) = 0 := by
  have hcomp : image.ι f ≫ cokernel.π f = 0 := by
    apply (cancel_epi (factorThruImage f)).mp
    simp only [image.fac_assoc, cokernel.condition, comp_zero]
  exact congrArg (fun k : image f ⟶ cokernel f => k.hom.app (op ⊤) v) hcomp

set_option maxHeartbeats 800000 in
/-- If the protected section belongs to the actual image sheaf of a morphism from
such a direct image, its germ at the zero prime vanishes. -/
theorem protected_generic_germ_zero_of_closed_image (Z : Closeds (PrimeSpectrum.Top OpenRing))
    (hZ : Z ≠ ⊤) (K : (TopCat.of Z).Sheaf AddCommGrpCat.{0})
    (f : directImage Z K ⟶ cokernel topDifferential)
    (v : (image f).obj.obj (op ⊤))
    (hv : (image.ι f).hom.app (op ⊤) v = protectedCokernelSection ⊤) :
    protectedGenericGerm = 0 := by
  have hω := image_section_cokernel (A := OpenRing) f v
  rw [hv] at hω
  apply cokernel_zero_on_nonempty_open_iff_generic_germ.mp
  refine ⟨Z.compl, ?_, ?_⟩
  · change ((Z : Set (PrimeSpectrum.Top OpenRing))ᶜ).Nonempty
    exact Set.nonempty_compl.mpr fun he => hZ (Closeds.coe_eq_univ.mp he)
  · exact (protectedCokernelSection_restrict (le_top : Z.compl ≤ ⊤)).symm.trans
      (restrict_eq_zero_of_mem_image Z K f (protectedCokernelSection ⊤) hω)

/-- The supported representative therefore supplies a rational primitive of the fixed four-form. -/
theorem protected_exact_of_closed_image (Z : Closeds (PrimeSpectrum.Top OpenRing))
    (hZ : Z ≠ ⊤) (K : (TopCat.of Z).Sheaf AddCommGrpCat.{0})
    (f : directImage Z K ⟶ cokernel topDifferential)
    (v : (image f).obj.obj (op ⊤))
    (hv : (image.ι f).hom.app (op ⊤) v = protectedCokernelSection ⊤) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA :=
  protected_exact_iff_generic_germ_zero.mpr (protected_generic_germ_zero_of_closed_image Z hZ K f v hv)

end CycleQ2LiteralResidueClosedSupport

end

#print axioms CycleQ2LiteralResidueClosedSupport.protected_exact_of_closed_image
