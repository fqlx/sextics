import Proposal.ScratchCechHyperVertex
import Proposal.ScratchTotalThreeChainMap

/-! The derived class of three compatible residue cochains on an open cover. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2.GlobalResidueClass
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenSections freeOpenMap)
open FreeCechResolution (coverChains)
open HomologicalComplex

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (AbSheaf X) ℤ)

abbrev Family (p : ℕ) (q : ℤ) :=
  ∀ a : Fin (p+1) → ι, (K.X q).obj.obj (op (FreeCech.intersection U a))

def horizontal {p : ℕ} {q : ℤ} (x : Family U K p q) : Family U K (p+1) q :=
  fun a ↦ ∑ i : Fin (p+2), ((-1 : ℤ)^i.val) •
    (K.X q).obj.map (FreeCech.faceInclusion U a i.succAbove).op (x (a ∘ i.succAbove))

def vertical {p : ℕ} {q : ℤ} (x : Family U K p q) : Family U K p (q+1) :=
  fun a ↦ (K.d q (q+1)).hom.app _ (x a)

abbrev represent {p : ℕ} {q : ℤ} (x : Family U K p q) : (coverChains U).X p ⟶ K.X q :=
  (FreeCech.sections U (K.X q) (Fin (p+1))).symm x

theorem represent_horizontal {p : ℕ} {q : ℤ} (x : Family U K p q) :
    represent U K (horizontal U K x) = (coverChains U).d (p+1) p ≫ represent U K x := by
  apply (FreeCech.sections U (K.X q) (Fin (p+2))).injective
  funext a
  rw [FreeCechResolution.sections_coverChains_d]
  simp [represent, horizontal]

theorem represent_vertical {p : ℕ} {q : ℤ} (x : Family U K p q) :
    represent U K (vertical U K x) = represent U K x ≫ K.d q (q+1) := by
  apply (FreeCech.sections U (K.X (q+1)) (Fin (p+1))).injective
  funext a
  rw [FreeCech.sections_postcomp]
  simp [represent, vertical]

/-- The unsigned Poincaré residues on vertices, double intersections and triple
intersections, with their actual differential and restriction equations. -/
structure Residues where
  vertices : Family U K 0 3
  edges : Family U K 1 2
  triangles : Family U K 2 1
  closed : vertical U K vertices = 0
  pairs : horizontal U K vertices = -vertical U K edges
  triples : horizontal U K edges = vertical U K triangles
  quadruples : horizontal U K triangles = 0

variable {U K}

def signed (s : Residues U K) : TotalThreeChainMap.Cocycle (coverChains U) K where
  f0 := represent U K s.vertices
  f1 := -represent U K s.edges
  f2 := represent U K s.triangles
  f3 := 0
  closed := by rw [← represent_vertical, s.closed]; exact map_zero _
  compat1 := by rw [← represent_horizontal, s.pairs, Preadditive.neg_comp,
    ← represent_vertical]; exact map_neg _ _
  compat2 := by rw [Preadditive.comp_neg, ← represent_horizontal, s.triples,
    represent_vertical]
  compat3 := by rw [← represent_horizontal, s.quadruples, zero_comp]; exact map_zero _
  compat4 := by simp

variable [HasDerivedCategory (AbSheaf X)]

/-- A class in genuine hypercohomology, represented by the cover augmentation
on the left and the signed residue chain map on the right. -/
def properClass (hc : (⨆ i, U i) = ⊤) (s : Residues U K) :
    DerivedCategory.Q.obj ((single (AbSheaf X) (ComplexShape.up ℤ) (3 : ℤ)).obj
      (freeOpen (⊤ : Opens X))) ⟶ DerivedCategory.Q.obj K :=
  CechHyperVertex.classOfCover U 3 hc (TotalThreeChainMap.chainMap (signed s))

theorem properClass_restrict (hc : (⨆ i, U i) = ⊤) (s : Residues U K) (i : ι) :
    DerivedCategory.Q.map ((single (AbSheaf X) (ComplexShape.up ℤ) (3 : ℤ)).map
      (freeOpenMap (show U i ≤ ⊤ from le_top))) ≫ properClass hc s =
    DerivedCategory.Q.map (CechHyperRoof.vertexCocycle 3 (FreeCech.vertexSheafMap U i)
      (TotalThreeChainMap.chainMap (signed s))) :=
  CechHyperVertex.classOfCover_restrict U 3 hc i _

/-- The chosen vertex evaluates to the first residue component as an actual
section on that chart. -/
theorem properClass_vertex_section (s : Residues U K) (i : ι) :
    freeOpenSections (K.X 3) (U i)
      ((singleObjXSelf (ComplexShape.up ℤ) 3 (freeOpen (U i))).inv ≫
        (CechHyperRoof.vertexCocycle 3 (FreeCech.vertexSheafMap U i)
          (TotalThreeChainMap.chainMap (signed s))).f 3) =
    (K.X 3).obj.map (FreeCech.vertexInclusion U i).op (s.vertices (fun _ ↦ i)) := by
  rw [CechHyperVertex.vertexCocycle_section, TotalThreeChainMap.chainMap_vertex]
  simp [signed, represent]

end CycleQ2.GlobalResidueClass
end
#print axioms CycleQ2.GlobalResidueClass.properClass
#print axioms CycleQ2.GlobalResidueClass.properClass_vertex_section
