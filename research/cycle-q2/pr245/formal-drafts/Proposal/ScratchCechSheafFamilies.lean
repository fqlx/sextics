import Proposal.ScratchGlobalResidueNat
import Proposal.ScratchMathlibCechDeRham
import Proposal.ScratchCechComplexFaces

/-! Transfer genuine Mathlib Čech cochains to the section families of
the free-open chain resolution, preserving cofaces and exterior derivatives. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite TopologicalSpace

namespace CycleQ2.Cech.SheafFamilies

open CycleQ2InjectiveCech (AbSheaf)
open GlobalResidueClass

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (K : CochainComplex (AbSheaf X) ℕ)

abbrev underlying := ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}
  ).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
abbrev double := presheafDouble U (underlying K)

/-- The normalization from the dependent finite product in Mathlib to the
literal infimum in the lattice of scheme opens. -/
def fromInf {p : ℕ} (a : Fin (p+1) → ι) :
    FreeCech.intersection U a ⟶ intersection U a :=
  eqToHom (intersection_eq_iInf U a).symm

def family (p q : ℕ) : (double U K).X p q →+ FamilyNat U K p q where
  toFun z a := (K.X q).obj.map (fromInf U a).op (component U (K.X q).obj a z)
  map_zero' := by funext a; simp
  map_add' x y := by funext a; simp

theorem singleton (q : ℕ) (i : ι) (z : (double U K).X 0 q) :
    (K.X q).obj.map (FreeCech.vertexInclusion U i).op (family U K 0 q z (fun _ => i)) =
      vertex U (K.X q).obj i z := by
  change (((K.X q).obj.map (fromInf U (fun _ : Fin 1 => i)).op ≫
      (K.X q).obj.map (FreeCech.vertexInclusion U i).op) _) =
    (K.X q).obj.map (singletonLift U i).op _
  rw [← (K.X q).obj.map_comp]
  rfl

theorem horizontal {p q : ℕ} (z : (double U K).X p q) :
    family U K (p+1) q ((double U K).h p q z) = horizontalNat U K (family U K p q z) := by
  funext a
  change (K.X q).obj.map (fromInf U a).op
    (component U (K.X q).obj a (((cechComplexFunctor U).obj (K.X q).obj).d p (p+1) z)) = _
  rw [horizontal_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  apply congrArg (_ • ·)
  change (((K.X q).obj.map (faceRestriction U a i).op ≫
    (K.X q).obj.map (fromInf U a).op) _) =
      (((K.X q).obj.map (fromInf U (a ∘ i.succAbove)).op ≫
       (K.X q).obj.map (FreeCech.faceInclusion U a i.succAbove).op) _)
  rw [← (K.X q).obj.map_comp,← (K.X q).obj.map_comp]
  rfl

theorem vertical {p q : ℕ} (z : (double U K).X p q) :
    family U K p (q+1) ((double U K).v p q z) = verticalNat U K (family U K p q z) := by
  funext a
  let f := (K.d q (q+1)).hom
  have h := ConcreteCategory.congr_hom (component_naturality U f a) z
  have hn := ConcreteCategory.congr_hom (f.naturality (fromInf U a).op)
    (component U (K.X q).obj a z)
  exact (congrArg ((K.X (q+1)).obj.map (fromInf U a).op) h).trans hn.symm

/-- The closed unsigned residue tuple in the free-open chain model. -/
def residues (a : (double U K).X 0 3) (b : (double U K).X 1 2)
    (c : (double U K).X 2 1) (ha : (double U K).v 0 3 a = 0)
    (hb : (double U K).h 0 3 a = -((double U K).v 1 2 b))
    (hc : (double U K).h 1 2 b = (double U K).v 2 1 c)
    (hd : (double U K).h 2 1 c = 0) : ResiduesNat U K where
  vertices := family U K 0 3 a
  edges := family U K 1 2 b
  triangles := family U K 2 1 c
  closed := by rw [← vertical,ha,map_zero]
  pairs := by rw [← horizontal,← vertical,hb,map_neg]
  triples := by rw [← horizontal,← vertical,hc]
  quadruples := by rw [← horizontal,hd,map_zero]

end CycleQ2.Cech.SheafFamilies
end

#print axioms CycleQ2.Cech.SheafFamilies.residues
