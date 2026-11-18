import Proposal.GeometricLiteralResidueDerivedSupport

/-!
# Degree-four support in a correspondence complex

If degree four of a sheaf complex comes from a closed subset, its cycles
and its fourth cohomology vanish on the open complement. A factorization
of the protected class through the resulting derived object therefore
produces a rational primitive without a separate comparison for its
fourth cohomology sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralResidueCochainSupport

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open CycleQ2GeometricAffineCohomology CycleQ2GeometricRegularDeRham CycleQ2AffineClearing
open CycleQ2LiteralResidueSheaf CycleQ2LiteralResidueExactness CycleQ2LiteralResidueDerived
open CycleQ2LiteralResidueClosedSupport CycleQ2LiteralResidueDerivedSupport
open CycleQ2InjectiveCech (freeOpen freeOpenSections)
open CycleQ2CechTwoToDerived (app app_injective freeOpenSections_postcomp)

attribute [local instance] HasDerivedCategory.standard

variable {A : Type} [CommRing A]

/-- An epimorphism of sheaves transmits vanishing of all sections over
subopens of a fixed open. The required lifts are local. -/
theorem subsingleton_sections_of_epi {F G : AbSheaf A} (p : F ⟶ G) [Epi p]
    (U : Opens (PrimeSpectrum.Top A))
    (hF : ∀ V ≤ U, Subsingleton (F.obj.obj (op V))) :
    Subsingleton (G.obj.obj (op U)) := by
  have : Sheaf.IsLocallySurjective p :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat p).mpr inferInstance
  suffices h : ∀ w : G.obj.obj (op U), w = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro w
  apply TopCat.Presheaf.IsSheaf.section_ext G.property
  intro x hx
  obtain ⟨V, i, ⟨v, hv⟩, hxV⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology (PrimeSpectrum.Top A)) p.hom w x hx
  refine ⟨V, leOfHom i, hxV, ?_⟩
  have := hF V (leOfHom i)
  change G.obj.map i.op w = G.obj.map i.op 0
  rw [← hv, Subsingleton.elim v 0, map_zero, map_zero]

/-- A closed support for a term suffices to annihilate the corresponding
cohomology sheaf on the whole complement. -/
theorem homology_sections_off (S : CochainComplex (AbSheaf A) ℤ) (n : ℤ)
    (Z : Closeds (PrimeSpectrum.Top A)) (T : (TopCat.of Z).Sheaf AddCommGrpCat.{0})
    (e : S.X n ≅ directImage Z T) :
    Subsingleton (((DerivedCategory.homologyFunctor (AbSheaf A) n).obj
      (DerivedCategory.Q.obj S)).obj.obj (op Z.compl)) := by
  have hcycles (V : Opens (PrimeSpectrum.Top A)) (hV : V ≤ Z.compl) :
      Subsingleton ((S.cycles n).obj.obj (op V)) := by
    have := sections_subsingleton_off Z T V hV
    exact (app_injective (S.iCycles n ≫ e.hom) V).subsingleton
  have := subsingleton_sections_of_epi (S.homologyπ n) Z.compl hcycles
  let e' : (DerivedCategory.homologyFunctor (AbSheaf A) n).obj (DerivedCategory.Q.obj S) ≅
      S.homology n := (DerivedCategory.homologyFunctorFactors (AbSheaf A) n).app S
  exact (app_injective e'.hom Z.compl).subsingleton

private theorem exact_of_section_factor (U : Jacobian.Opens) (hU : U.carrier.Nonempty)
    (M : AbSheaf OpenRing) [Subsingleton (M.obj.obj (op U))]
    (u : freeOpen (X := PrimeSpectrum.Top OpenRing) ⊤ ⟶ M) (f : M ⟶ cokernel topDifferential)
    (h : u ≫ f = protectedSectionMap ⊤ ≫ cokernel.π topDifferential) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  apply protected_exact_iff_cokernel_zero_on_nonempty_open.mpr
  refine ⟨U, hU, ?_⟩
  let v := freeOpenSections M ⊤ u
  have hs : f.hom.app (op ⊤) v = protectedCokernelSection ⊤ := by
    have he := ((freeOpenSections_postcomp ⊤ u f).trans
      (congrArg (freeOpenSections (cokernel topDifferential) ⊤) h)).trans
      (freeOpenSections_postcomp ⊤ (protectedSectionMap ⊤) (cokernel.π topDifferential)).symm
    have hid : freeOpenSections additiveFunctions ⊤ (protectedSectionMap ⊤) = protectedSection ⊤ :=
      AddEquiv.apply_symm_apply _ _
    rw [hid] at he
    exact he
  let i : U ⟶ ⊤ := homOfLE le_top
  have hv : M.obj.map i.op v = 0 := Subsingleton.elim _ _
  exact (protectedCokernelSection_restrict (U := ⊤) (V := U) le_top).symm.trans
    ((congrArg ((cokernel topDifferential).obj.map i.op) hs.symm).trans
      ((NatTrans.naturality_apply f.hom i.op v).symm.trans
        ((congrArg (f.hom.app _) hv).trans (map_zero _))))

/-- A correspondence factoring through a complex with a closed-supported
fourth term yields exactness of the literal protected residue. -/
theorem protected_exact_of_closed_cochain_factor
    (K : CochainComplex (AbSheaf OpenRing) ℤ)
    (three : K.X 3 ≅ additiveForms) (four : K.X 4 ≅ additiveFunctions)
    (hd : K.d 3 4 ≫ four.hom = three.hom ≫ topDifferential) (htop : K.d 4 5 = 0)
    (Z : Closeds (PrimeSpectrum.Top OpenRing)) (hZ : Z ≠ ⊤)
    (T : (TopCat.of Z).Sheaf AddCommGrpCat.{0}) (S : CochainComplex (AbSheaf OpenRing) ℤ)
    (supp : S.X 4 ≅ directImage Z T)
    (a : (DerivedCategory.singleFunctor (AbSheaf OpenRing) 4).obj
      (freeOpen (X := PrimeSpectrum.Top OpenRing) ⊤) ⟶ DerivedCategory.Q.obj S)
    (b : DerivedCategory.Q.obj S ⟶ DerivedCategory.Q.obj K)
    (hfactor : DerivedCategory.Q.map (protectedCocycle ⊤ K four htop) = a ≫ b) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  obtain ⟨u, v, huv⟩ :=
    factor_cokernel K 4 (protectedSectionMap ⊤ ≫ four.inv) _ (DerivedCategory.Q.obj S) a b hfactor
  have := homology_sections_off S 4 Z T supp
  have hU : Z.compl.carrier.Nonempty :=
    Set.nonempty_compl.mpr (fun he => hZ (Closeds.coe_eq_univ.mp he))
  let q := cokernel.π topDifferential
  let p : cokernel (K.d 3 4) ⟶ cokernel topDifferential :=
    cokernel.desc _ (four.hom ≫ q) (by
      rw [← Category.assoc, hd, Category.assoc, cokernel.condition, comp_zero])
  apply exact_of_section_factor Z.compl hU _ u (v ≫ p)
  calc
    _ = (u ≫ v) ≫ p := (Category.assoc _ _ _).symm
    _ = ((protectedSectionMap ⊤ ≫ four.inv) ≫ cokernel.π (K.d 3 4)) ≫ p := congrArg (· ≫ p) huv
    _ = _ := by simp [p, q, Category.assoc]

/-- Apply the actual direct image of sheaves along the closed inclusion in each degree. -/
def closedPushforwardComplex (Z : Closeds (PrimeSpectrum.Top A))
    (S : CochainComplex (CycleQ2InjectiveCech.AbSheaf (TopCat.of Z)) ℤ) :
    CochainComplex (AbSheaf A) ℤ :=
  let F : CycleQ2InjectiveCech.AbSheaf (TopCat.of Z) ⥤ AbSheaf A :=
    TopCat.Sheaf.pushforward AddCommGrpCat.{0} (closedInclusion Z)
  letI : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj S

/-- For an actual complex on the divisor the closed support needed for the
rational primitive is automatic. -/
theorem protected_exact_of_closed_pushforward
    (K : CochainComplex (AbSheaf OpenRing) ℤ)
    (three : K.X 3 ≅ additiveForms) (four : K.X 4 ≅ additiveFunctions)
    (hd : K.d 3 4 ≫ four.hom = three.hom ≫ topDifferential) (htop : K.d 4 5 = 0)
    (Z : Closeds (PrimeSpectrum.Top OpenRing)) (hZ : Z ≠ ⊤)
    (S : CochainComplex (CycleQ2InjectiveCech.AbSheaf (TopCat.of Z)) ℤ)
    (a : (DerivedCategory.singleFunctor (AbSheaf OpenRing) 4).obj
      (freeOpen (X := PrimeSpectrum.Top OpenRing) ⊤) ⟶
        DerivedCategory.Q.obj (closedPushforwardComplex Z S))
    (b : DerivedCategory.Q.obj (closedPushforwardComplex Z S) ⟶ DerivedCategory.Q.obj K)
    (hfactor : DerivedCategory.Q.map (protectedCocycle ⊤ K four htop) = a ≫ b) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA :=
  protected_exact_of_closed_cochain_factor K three four hd htop Z hZ (S.X 4)
    (closedPushforwardComplex Z S) (Iso.refl _) a b hfactor

end CycleQ2LiteralResidueCochainSupport
end

#print axioms CycleQ2LiteralResidueCochainSupport.protected_exact_of_closed_pushforward
