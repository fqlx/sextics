import Proposal.GeometricLiteralResidueDerived
import Proposal.GeometricLiteralResidueClosedSupport

/-!
# From support of a derived correspondence to the protected rational primitive

If the protected derived cocycle factors through a complex whose fourth
cohomology sheaf comes from a proper closed subset, its image in the
cokernel of the top exterior differential has the same support. Applying the
fourth cohomology functor to the factorization supplies the actual section
of the image sheaf used for rational exactness.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralResidueDerivedSupport

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open CycleQ2GeometricAffineCohomology CycleQ2GeometricRegularDeRham CycleQ2AffineClearing
open CycleQ2LiteralResidueSheaf CycleQ2LiteralResidueExactness CycleQ2LiteralResidueDerived
open CycleQ2LiteralResidueClosedSupport
open CycleQ2InjectiveCech (freeOpen freeOpenSections)
open CycleQ2CechTwoToDerived (freeOpenSections_postcomp)

universe u v w

/-- A derived factorization of a map of single complexes factors the
underlying morphism through the cohomology of the middle complex. -/
theorem factor_through_homology {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (n : ℤ) {A B : C} (f : A ⟶ B)
    (L : DerivedCategory C) (a : (DerivedCategory.singleFunctor C n).obj A ⟶ L)
    (b : L ⟶ (DerivedCategory.singleFunctor C n).obj B)
    (h : (DerivedCategory.singleFunctor C n).map f = a ≫ b) :
    ∃ (g : A ⟶ (DerivedCategory.homologyFunctor C n).obj L)
      (j : (DerivedCategory.homologyFunctor C n).obj L ⟶ B), g ≫ j = f := by
  let H := DerivedCategory.homologyFunctor C n
  let e := DerivedCategory.singleFunctorCompHomologyFunctorIso C n
  refine ⟨(e.app A).inv ≫ H.map a, H.map b ≫ (e.app B).hom, ?_⟩
  rw [Category.assoc, ← Category.assoc (H.map a), ← Functor.map_comp, ← h]
  exact NatIso.naturality_1 e f

/-- Projection of a derived cocycle factorization to the incoming cokernel. -/
theorem factor_cokernel {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (K : CochainComplex C ℤ) (n : ℤ) {A : C}
    (α : A ⟶ K.X n) (hα : ∀ j : ℤ, (ComplexShape.up ℤ).Rel n j → α ≫ K.d n j = 0)
    (L : DerivedCategory C) (a : (DerivedCategory.singleFunctor C n).obj A ⟶ L)
    (b : L ⟶ DerivedCategory.Q.obj K)
    (hfactor : DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle α hα) = a ≫ b) :
    ∃ (u : A ⟶ (DerivedCategory.homologyFunctor C n).obj L)
      (v : (DerivedCategory.homologyFunctor C n).obj L ⟶ cokernel (K.d (n - 1) n)),
      u ≫ v = α ≫ cokernel.π (K.d (n - 1) n) := by
  let π := CycleQ2GeometricResidueDerivedEdge.cokernelProjection K n
  have hc : HomologicalComplex.mkHomFromSingle α hα ≫ π =
      (HomologicalComplex.single _ (ComplexShape.up ℤ) n).map
        (α ≫ cokernel.π (K.d (n - 1) n)) := by
    apply HomologicalComplex.from_single_hom_ext
    simp [π, CycleQ2GeometricResidueDerivedEdge.cokernelProjection,
      HomologicalComplex.single_map_f_self]
  apply factor_through_homology n _ L a (b ≫ DerivedCategory.Q.map π)
  change DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).map _) = _
  rw [← hc, Functor.map_comp, hfactor, Category.assoc]

attribute [local instance] HasDerivedCategory.standard

private theorem exact_of_closed_section_factor
    (Z : Closeds (PrimeSpectrum.Top OpenRing)) (hZ : Z ≠ ⊤)
    (T : (TopCat.of Z).Sheaf AddCommGrpCat.{0})
    (u : freeOpen (X := PrimeSpectrum.Top OpenRing) ⊤ ⟶ directImage Z T)
    (f : directImage Z T ⟶ cokernel topDifferential)
    (h : u ≫ f = protectedSectionMap ⊤ ≫ cokernel.π topDifferential) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  let m := u ≫ factorThruImage f
  have hm : m ≫ image.ι f = protectedSectionMap ⊤ ≫ cokernel.π topDifferential := by
    rw [show m = u ≫ factorThruImage f from rfl, Category.assoc, image.fac, h]
  apply protected_exact_of_closed_image Z hZ T f (freeOpenSections (image f) ⊤ m)
  have hsec := (freeOpenSections_postcomp ⊤ m (image.ι f)).trans
    (congrArg (freeOpenSections (cokernel topDifferential) ⊤) hm)
  have he := hsec.trans
    (freeOpenSections_postcomp ⊤ (protectedSectionMap ⊤) (cokernel.π topDifferential)).symm
  have hid : freeOpenSections additiveFunctions ⊤ (protectedSectionMap ⊤) = protectedSection ⊤ :=
    AddEquiv.apply_symm_apply _ _
  rw [hid] at he
  exact he

/-- It suffices for the geometric correspondence to factor the protected
class through a derived object with fourth cohomology on a proper closed
subset. Its other cohomology sheaves are unrestricted. -/
theorem protected_exact_of_derived_closed_factor
    (K : CochainComplex (AbSheaf OpenRing) ℤ)
    (three : K.X 3 ≅ additiveForms) (four : K.X 4 ≅ additiveFunctions)
    (hd : K.d 3 4 ≫ four.hom = three.hom ≫ topDifferential) (htop : K.d 4 5 = 0)
    (Z : Closeds (PrimeSpectrum.Top OpenRing)) (hZ : Z ≠ ⊤)
    (T : (TopCat.of Z).Sheaf AddCommGrpCat.{0})
    (L : DerivedCategory (AbSheaf OpenRing))
    (supp : (DerivedCategory.homologyFunctor (AbSheaf OpenRing) 4).obj L ≅ directImage Z T)
    (a : (DerivedCategory.singleFunctor (AbSheaf OpenRing) 4).obj
      (freeOpen (X := PrimeSpectrum.Top OpenRing) ⊤) ⟶ L)
    (b : L ⟶ DerivedCategory.Q.obj K)
    (hfactor : DerivedCategory.Q.map (protectedCocycle ⊤ K four htop) = a ≫ b) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  obtain ⟨u, v, huv⟩ := factor_cokernel K 4 (protectedSectionMap ⊤ ≫ four.inv) _ L a b hfactor
  let q := cokernel.π topDifferential
  let p : cokernel (K.d 3 4) ⟶ cokernel topDifferential :=
    cokernel.desc _ (four.hom ≫ q) (by
      rw [← Category.assoc, hd, Category.assoc, cokernel.condition, comp_zero])
  apply exact_of_closed_section_factor Z hZ T (u ≫ supp.hom) (supp.inv ≫ v ≫ p)
  calc
    _ = (u ≫ v) ≫ p := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = ((protectedSectionMap ⊤ ≫ four.inv) ≫ cokernel.π (K.d 3 4)) ≫ p :=
      congrArg (· ≫ p) huv
    _ = _ := by simp [p, q, Category.assoc]

end CycleQ2LiteralResidueDerivedSupport
end

#print axioms CycleQ2LiteralResidueDerivedSupport.protected_exact_of_derived_closed_factor
