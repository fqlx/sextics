import Proposal.ScratchGlobalResidueClass

/-! Nonnegative sheaf complexes and the global residue class in degree three. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2.GlobalResidueClass
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenSections freeOpenMap)
open HomologicalComplex

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (AbSheaf X) ℕ)

abbrev integerComplex := K.extend ComplexShape.embeddingUpNat
abbrev inDegree (q : ℕ) : (integerComplex K).X (q : ℤ) ≅ K.X q :=
  K.extendXIso ComplexShape.embeddingUpNat (i := q) rfl

abbrev FamilyNat (p q : ℕ) :=
  ∀ a : Fin (p+1) → ι, (K.X q).obj.obj (op (FreeCech.intersection U a))

def horizontalNat {p q : ℕ} (x : FamilyNat U K p q) : FamilyNat U K (p+1) q :=
  fun a ↦ ∑ i : Fin (p+2), ((-1 : ℤ)^i.val) •
    (K.X q).obj.map (FreeCech.faceInclusion U a i.succAbove).op (x (a ∘ i.succAbove))

def verticalNat {p q : ℕ} (x : FamilyNat U K p q) : FamilyNat U K p (q+1) :=
  fun a ↦ (K.d q (q+1)).hom.app _ (x a)

def extendFamily (p q : ℕ) :
    FamilyNat U K p q →+ Family U (integerComplex K) p (q : ℤ) where
  toFun x a := (inDegree K q).inv.hom.app _ (x a)
  map_zero' := by funext a; exact map_zero _
  map_add' x y := by funext a; exact map_add _ _ _

theorem extendFamily_horizontal {p q : ℕ} (x : FamilyNat U K p q) :
    horizontal U (integerComplex K) (extendFamily U K p q x) =
      extendFamily U K (p+1) q (horizontalNat U K x) := by
  funext a
  change (∑ i : Fin (p+2), _ • _ ) = (inDegree K q).inv.hom.app _ (∑ i : Fin (p+2), _ • _)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  exact congrArg (_ • ·) (NatTrans.naturality_apply (inDegree K q).inv.hom
    (FreeCech.faceInclusion U a i.succAbove).op (x (a ∘ i.succAbove))).symm

theorem extendFamily_vertical {p q : ℕ} (x : FamilyNat U K p q) :
    vertical U (integerComplex K) (extendFamily U K p q x) =
      extendFamily U K p (q+1) (verticalNat U K x) := by
  funext a
  have hd : (inDegree K q).inv ≫ (integerComplex K).d (q : ℤ) ((q+1 : ℕ) : ℤ) =
      K.d q (q+1) ≫ (inDegree K (q+1)).inv := by
    rw [K.extend_d_eq ComplexShape.embeddingUpNat (i := q) (j := q+1) rfl rfl]
    simp [inDegree]
  exact congrArg (fun f : K.X q ⟶ (integerComplex K).X ((q+1 : ℕ) : ℤ) ↦
    f.hom.app (op (FreeCech.intersection U a)) (x a)) hd

structure ResiduesNat where
  vertices : FamilyNat U K 0 3
  edges : FamilyNat U K 1 2
  triangles : FamilyNat U K 2 1
  closed : verticalNat U K vertices = 0
  pairs : horizontalNat U K vertices = -verticalNat U K edges
  triples : horizontalNat U K edges = verticalNat U K triangles
  quadruples : horizontalNat U K triangles = 0

def ResiduesNat.toResidues (s : ResiduesNat U K) : Residues U (integerComplex K) where
  vertices := extendFamily U K 0 3 s.vertices
  edges := extendFamily U K 1 2 s.edges
  triangles := extendFamily U K 2 1 s.triangles
  closed := by rw [extendFamily_vertical, s.closed, map_zero]
  pairs := by rw [extendFamily_horizontal, extendFamily_vertical, s.pairs, map_neg]
  triples := by rw [extendFamily_horizontal, extendFamily_vertical, s.triples]
  quadruples := by rw [extendFamily_horizontal, s.quadruples, map_zero]

variable [HasDerivedCategory (AbSheaf X)]

def properClassNat (hc : (⨆ i, U i) = ⊤) (s : ResiduesNat U K) :
    DerivedCategory.Q.obj ((single (AbSheaf X) (ComplexShape.up ℤ) (3 : ℤ)).obj
      (freeOpen (⊤ : Opens X))) ⟶ DerivedCategory.Q.obj (integerComplex K) :=
  properClass hc (s.toResidues U K)

/-- The roof restricted to a chart has its usual degree-three cocycle
representative even for the nonnegatively indexed input. -/
theorem properClassNat_restrict (hc : (⨆ i, U i) = ⊤) (s : ResiduesNat U K) (i : ι) :
    DerivedCategory.Q.map ((single (AbSheaf X) (ComplexShape.up ℤ) (3 : ℤ)).map
      (freeOpenMap (show U i ≤ ⊤ from le_top))) ≫ properClassNat U K hc s =
      DerivedCategory.Q.map (CechHyperRoof.vertexCocycle 3 (FreeCech.vertexSheafMap U i)
        (TotalThreeChainMap.chainMap (signed (s.toResidues U K)))) :=
  properClass_restrict hc (s.toResidues U K) i

/-- Transport back through extension by zero recovers exactly the input
residue on the chart. -/
theorem properClassNat_vertex_section (s : ResiduesNat U K) (i : ι) :
    (inDegree K 3).hom.hom.app (op (U i))
      (freeOpenSections ((integerComplex K).X (3 : ℤ)) (U i)
        ((singleObjXSelf (ComplexShape.up ℤ) (3 : ℤ) (freeOpen (U i))).inv ≫
          (CechHyperRoof.vertexCocycle 3 (FreeCech.vertexSheafMap U i)
            (TotalThreeChainMap.chainMap (signed (s.toResidues U K)))).f 3)) =
      (K.X 3).obj.map (FreeCech.vertexInclusion U i).op (s.vertices (fun _ ↦ i)) := by
  rw [properClass_vertex_section, NatTrans.naturality_apply]
  apply congrArg ((K.X 3).obj.map (FreeCech.vertexInclusion U i).op)
  change (inDegree K 3).hom.hom.app _
    ((inDegree K 3).inv.hom.app _ (s.vertices (fun _ ↦ i))) = _
  exact congrArg (fun f : K.X 3 ⟶ K.X 3 ↦ f.hom.app _ (s.vertices (fun _ ↦ i)))
    (inDegree K 3).inv_hom_id

end CycleQ2.GlobalResidueClass
end
#print axioms CycleQ2.GlobalResidueClass.properClassNat
