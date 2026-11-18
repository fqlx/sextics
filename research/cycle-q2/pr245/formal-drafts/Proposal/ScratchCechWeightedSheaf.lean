import Proposal.ScratchCechWeightedGoodComplex
import Proposal.ScratchCechBasisSheafification
import Proposal.ScratchWeightedNativeCech
import Proposal.ScratchMathlibCechDeRham
import Proposal.ScratchCechTotalThreeMap

/-! A global complex of abelian sheaves on the weighted hypersurface and a
map on the full Čech total cohomology from its affine intersection forms. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricHodgeThreefold CycleQ2WeightedResidueAtlas CycleQ2GenericSexticGradient
open CycleQ2CechDeRhamTotalThree

namespace CycleQ2.Cech.WeightedSheaf

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)

/-- Ordinary de Rham sheaf complex, using compatible presentations over the
affine basis. -/
abbrev K := BasisSheafification.sheafComplex (threefold φ : TopCat) (WeightedGoodComplex.complex φ)
abbrev forgetK := ((sheafToPresheaf (BasisSheafification.J (threefold φ : TopCat)) AddCommGrpCat.{0}
    ).mapHomologicalComplex (ComplexShape.up ℕ)).obj (K φ)
abbrev sheafDouble := presheafDouble (U φ) (forgetK φ)

def toGlobal (n : ℕ) : WeightedGoodComplex.A φ n ⟶ (forgetK φ).X n :=
  WeightedGoodComplex.fromForms φ n ≫
    (BasisSheafification.sheafComplexUnit _ (WeightedGoodComplex.complex φ)).f n

theorem toGlobal_d {W : (threefold φ).Opens} (hW : WeightedBasis.Good φ W)
    {I : Type} [Fintype I] [LinearOrder I]
    (b : Module.Basis I (Native.R (toBase φ) W) (KaehlerDifferential k (Native.R (toBase φ) W)))
    (x : I → Native.R (toBase φ) W)
    (hx : ∀ j, b j = KaehlerDifferential.D k (Native.R (toBase φ) W) (x j))
    (n : ℕ) (s : (WeightedGoodComplex.A φ n).obj (op W)) :
    ((forgetK φ).d n (n+1)).app (op W) ((toGlobal φ n).app (op W) s) =
      (toGlobal φ (n+1)).app (op W) (CycleQ2LogarithmicDifferential.exteriorD b n s) := by
  let η := BasisSheafification.sheafComplexUnit (threefold φ : TopCat) (WeightedGoodComplex.complex φ)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (η.comm n (n+1)) (op W))
    ((WeightedGoodComplex.fromForms φ n).app (op W) s)
  exact h.trans (congrArg ((η.f (n+1)).app (op W))
    (WeightedGoodComplex.fromForms_d φ hW b x hx n s))

private theorem cochain_eval {P Q : (threefold φ).Opensᵒᵖ ⥤ AddCommGrpCat.{0}}
    (g : P ⟶ Q) {p : ℕ} (v : Fin (p+1) → Index)
    (s : ((cechComplexFunctor (U φ)).obj P).X p) :
    component (U φ) Q v (((cechComplexFunctor (U φ)).map g).f p s) =
      g.app (op (intersection (U φ) v)) (component (U φ) P v s) :=
  ConcreteCategory.congr_hom (component_naturality (U φ) g v) s

private theorem good_simplex {p : ℕ} (x : Fin (p+1) → Index) :
    WeightedBasis.Good φ (intersection (U φ) x) := by
  rw [intersection_eq_iInf]
  exact WeightedBasis.good_intersection φ x

/-- The map on the actual Čech complexes induced by sheafifying all affine terms. -/
def toSheafDouble : DoubleMap (CycleQ2WeightedNativeCech.double φ) (sheafDouble φ) where
  app p q := (((cechComplexFunctor (U φ)).map (toGlobal φ q)).f p).hom
  horizontal p q s :=
    (ConcreteCategory.congr_hom (((cechComplexFunctor (U φ)).map (toGlobal φ q)).comm p (p+1)) s).symm
  vertical p q s := by
    apply (sectionsEquiv (U φ) ((forgetK φ).X (q+1)) p).injective
    funext v
    simp only [sectionsEquiv_apply]
    change component (U φ) _ v (((cechComplexFunctor (U φ)).map (toGlobal φ (q+1))).f p
        (vertical (U φ) _ _ p q s)) =
      component (U φ) _ v (((cechComplexFunctor (U φ)).map ((forgetK φ).d q (q+1))).f p
        (((cechComplexFunctor (U φ)).map (toGlobal φ q)).f p s))
    rw [cochain_eval,component_vertical,cochain_eval,cochain_eval]
    let a := CycleQ2WeightedNativeCech.frames φ
    exact (toGlobal_d φ (good_simplex φ v) (a.basis p v) (a.coords p v) (a.exact_coord p v)
      q (component (U φ) _ v s)).symm

abbrev cohomologyMap := (toSheafDouble φ).onCohomology

/-- The vertex of a sheafified class is the image of the original ordinary
three-form in the global de Rham sheaf. -/
theorem vertex_image (i : Index) (z : Cycles (CycleQ2WeightedNativeCech.double φ)) :
    vertex (U φ) ((forgetK φ).X 3) i (((toSheafDouble φ).onCycles z).1.1) =
      (toGlobal φ 3).app (op (U φ i))
        (vertex (U φ) (WeightedGoodComplex.A φ 3) i z.1.1) :=
  ConcreteCategory.congr_hom (vertex_naturality (U φ) (toGlobal φ 3) i) z.1.1

/-- On the affine exact-coordinate basis, the construction recovers the
usual sheafification of the exterior-power presheaf in each degree. -/
def usualTermIso (hg : IsUnit (φ goodParameter)) (n : ℕ) :
    (presheafToSheaf (BasisSheafification.J (threefold φ : TopCat)) AddCommGrpCat.{0}).obj
      (WeightedGoodComplex.A φ n) ≅ (K φ).X n :=
  BasisSheafification.isoOfBasis (WeightedGoodComplex.fromForms φ n)
    {V | WeightedBasis.Good φ V} (WeightedBasis.isBasis φ hg)
    (fun V hV => by
      letI := WeightedGoodComplex.fromForms_isIso φ n V hV
      exact ConcreteCategory.bijective_of_isIso _)

end CycleQ2.Cech.WeightedSheaf
end

#print axioms CycleQ2.Cech.WeightedSheaf.toSheafDouble
#print axioms CycleQ2.Cech.WeightedSheaf.usualTermIso
