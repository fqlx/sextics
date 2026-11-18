import Proposal.ScratchCechWeightedSheaf
import Proposal.ScratchCechSheafFamilies

/-! The proper de Rham hypercohomology class attached to closed unsigned
residue components on the affine gradient intersections of the threefold. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricHodgeThreefold CycleQ2WeightedResidueAtlas CycleQ2GenericSexticGradient

namespace CycleQ2.Cech.WeightedSheaf
open CycleQ2WeightedNativeCech (double)

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)
    (a : (double φ).X 0 3) (b : (double φ).X 1 2) (c : (double φ).X 2 1)
    (ha : (double φ).v 0 3 a = 0)
    (hb : (double φ).h 0 3 a = -((double φ).v 1 2 b))
    (hc : (double φ).h 1 2 b = (double φ).v 2 1 c)
    (hd : (double φ).h 2 1 c = 0)

/-- Closed residues on genuine open intersections of the gradient cover,
as sections of the global sheaf de Rham complex. -/
def sheafResidues : GlobalResidueClass.ResiduesNat (U φ) (K φ) :=
  let f := toSheafDouble φ
  SheafFamilies.residues (U φ) (K φ) (f.app 0 3 a) (f.app 1 2 b) (f.app 2 1 c)
    (by rw [← f.vertical,ha,map_zero])
    (by rw [← f.horizontal,← f.vertical,hb,map_neg])
    (by rw [← f.horizontal,← f.vertical,hc])
    (by rw [← f.horizontal,hd,map_zero])

theorem sheafResidues_vertex (i : Index) :
    (((K φ).X 3).obj.map (FreeCech.vertexInclusion (U φ) i).op)
      ((sheafResidues φ a b c ha hb hc hd).vertices (fun _ => i)) =
    (toGlobal φ 3).app (op (U φ i))
      (vertex (U φ) (WeightedGoodComplex.A φ 3) i a) := by
  exact (SheafFamilies.singleton (U φ) (K φ) 3 i ((toSheafDouble φ).app 0 3 a)).trans
    (ConcreteCategory.congr_hom (vertex_naturality (U φ) (toGlobal φ 3) i) a)

variable [HasDerivedCategory (CycleQ2InjectiveCech.AbSheaf (threefold φ : TopCat))]

/-- An actual derived morphism on the proper weighted threefold. -/
abbrev properClass (hg : IsUnit (φ goodParameter)) :=
  GlobalResidueClass.properClassNat (U φ) (K φ) (cover φ hg)
    (sheafResidues φ a b c ha hb hc hd)

end CycleQ2.Cech.WeightedSheaf
end
#print axioms CycleQ2.Cech.WeightedSheaf.properClass
