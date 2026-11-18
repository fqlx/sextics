import Proposal.GeometricLiteralResidueExactness
import Proposal.GeometricResidueDerivedEdge
import Proposal.GeometricCartierDerivedClass

/-!
# Derived vanishing of the protected form implies rational exactness

The free abelian sheaf on an open represents sections over that open.
It therefore represents the literal protected form as a map into degree
four of a sheaf complex with the given top exterior differential.
Projection to the degree-four cokernel extracts the local primitives
from vanishing in the derived category. Lower degrees and the cover of
the open do not enter this implication.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralResidueDerived

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open CycleQ2GeometricAffineCohomology CycleQ2GeometricRegularDeRham CycleQ2AffineClearing
open CycleQ2LiteralResidueSheaf CycleQ2LiteralResidueExactness
open CycleQ2GeometricResidueDerivedEdge
open CycleQ2InjectiveCech (freeOpen freeOpenSections)
open CycleQ2CechTwoToDerived (freeOpenSections_postcomp)

attribute [local instance] HasDerivedCategory.standard

/-- The map representing the protected section on the chosen open. -/
def protectedSectionMap (U : Jacobian.Opens) :
    freeOpen (X := PrimeSpectrum.Top OpenRing) U ⟶ additiveFunctions :=
  (freeOpenSections additiveFunctions U).symm (protectedSection U)

/-- The protected four-form as a cocycle with coefficients in any complex
whose degree-four term is identified with the actual volume frame. -/
def protectedCocycle (U : Jacobian.Opens) (K : CochainComplex (AbSheaf OpenRing) ℤ)
    (e : K.X 4 ≅ additiveFunctions) (htop : K.d 4 5 = 0) :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 4).obj (freeOpen (X := PrimeSpectrum.Top OpenRing) U) ⟶ K :=
  HomologicalComplex.mkHomFromSingle (protectedSectionMap U ≫ e.inv) (fun j hj => by
    change 4 + 1 = j at hj
    subst j
    simp [htop])

/-- Vanishing of the actual section class in the derived category on a
nonempty open yields a rational Kähler primitive of the protected source.
The two term identifications specify only the terminal differential. -/
theorem protected_exact_of_derived_zero (U : Jacobian.Opens) (hU : U.carrier.Nonempty)
    (K : CochainComplex (AbSheaf OpenRing) ℤ)
    (three : K.X 3 ≅ additiveForms) (four : K.X 4 ≅ additiveFunctions)
    (hd : K.d 3 4 ≫ four.hom = three.hom ≫ topDifferential) (htop : K.d 4 5 = 0)
    (hzero : DerivedCategory.Q.map (protectedCocycle U K four htop) = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA := by
  apply protected_exact_iff_cokernel_zero_on_nonempty_open.mpr
  refine ⟨U, hU, ?_⟩
  have hc : (protectedSectionMap U ≫ four.inv) ≫ cokernel.π (K.d 3 4) = 0 :=
    comp_cokernel_eq_zero_of_derived_zero K 4 _ _ hzero
  let q := cokernel.π topDifferential
  let p : cokernel (K.d 3 4) ⟶ cokernel topDifferential :=
    cokernel.desc _ (four.hom ≫ q) (by
      rw [← Category.assoc, hd, Category.assoc, cokernel.condition, comp_zero])
  have hp : protectedSectionMap U ≫ q = 0 := by
    have h := congrArg (fun g => g ≫ p) hc
    simpa [p, Category.assoc] using h
  have hz := congrArg (freeOpenSections (cokernel topDifferential) U) hp
  rw [map_zero] at hz
  have hs := (freeOpenSections_postcomp U (protectedSectionMap U) q).trans hz
  have hid : freeOpenSections additiveFunctions U (protectedSectionMap U) = protectedSection U :=
    AddEquiv.apply_symm_apply _ _
  rw [hid] at hs
  exact hs

end CycleQ2LiteralResidueDerived
end

#print axioms CycleQ2LiteralResidueDerived.protected_exact_of_derived_zero
