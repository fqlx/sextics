import Proposal.ScratchGlobalResidueNat
import Proposal.ScratchNeighborhoodPrimitive
import Mathlib.Topology.Sheaves.Stalks
import Proposal.GeometricThreeOpenH2

/-! A vanishing proper residue has an actual regular primitive near each vertex point. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2.GlobalResidueClass
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenSections)

variable {X : TopCat.{0}} {ι : Type} {U : ι → Opens X}
variable {K : CochainComplex (AbSheaf X) ℤ} [HasDerivedCategory (AbSheaf X)]

/-- For a zero proper class, the literal vertex residue has a regular primitive
on some neighborhood of every chosen point. -/
theorem localPrimitive_of_properClass_zero (hc : (⨆ i, U i) = ⊤) (s : Residues U K)
    (hz : properClass hc s = 0) (i : ι) (x : X) (hx : x ∈ U i) :
    ∃ (V : Opens X) (hV : V ≤ U i), x ∈ V ∧
      ∃ η : (K.X 2).obj.obj (op V), (K.d 2 3).hom.app (op V) η =
        (K.X 3).obj.map (homOfLE hV).op
          ((K.X 3).obj.map (FreeCech.vertexInclusion U i).op (s.vertices (fun _ ↦ i))) := by
  let c := CechHyperRoof.vertexCocycle 3 (FreeCech.vertexSheafMap U i)
    (TotalThreeChainMap.chainMap (signed s))
  have hzero : DerivedCategory.Q.map c = 0 := by
    simpa [hz] using (properClass_restrict hc s i).symm
  obtain ⟨V, hV, hxV, η, hη⟩ := NeighborhoodPrimitive.of_derived_zero K 3 (U i) c hzero x hx
  exact ⟨V, hV, hxV, η, hη.trans (congrArg ((K.X 3).obj.map (homOfLE hV).op)
    (properClass_vertex_section s i))⟩

/-- The same local primitive gives a germ whose differential equals the actual
residue germ. In particular this applies at the generic point of the threefold. -/
theorem stalkPrimitive_of_properClass_zero (hc : (⨆ i, U i) = ⊤) (s : Residues U K)
    (hz : properClass hc s = 0) (i : ι) (x : X) (hx : x ∈ U i) :
    ∃ η : TopCat.Presheaf.stalk (K.X 2).obj x,
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (K.d 2 3).hom η =
        TopCat.Presheaf.germ (K.X 3).obj (U i) x hx
          ((K.X 3).obj.map (FreeCech.vertexInclusion U i).op (s.vertices (fun _ ↦ i))) := by
  obtain ⟨V, hV, hxV, η, hη⟩ := localPrimitive_of_properClass_zero hc s hz i x hx
  refine ⟨TopCat.Presheaf.germ (K.X 2).obj V x hxV η, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hη, TopCat.Presheaf.germ_res_apply]

/-- An additive sheaf morphism killing exact forms vanishes on the actual
input residue whenever the proper derived class is zero. -/
theorem annihilator_of_properClass_zero (hc : (⨆ i, U i) = ⊤) (s : Residues U K)
    (hz : properClass hc s = 0) (i : ι) {N : AbSheaf X} (e : K.X 3 ⟶ N)
    (he : K.d 2 3 ≫ e = 0) :
    e.hom.app (op (U i))
      ((K.X 3).obj.map (FreeCech.vertexInclusion U i).op (s.vertices (fun _ ↦ i))) = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext N.property
  intro x hx
  obtain ⟨V, hV, hxV, η, hη⟩ := localPrimitive_of_properClass_zero hc s hz i x hx
  refine ⟨V, hV, hxV, ?_⟩
  change N.obj.map (homOfLE hV).op (e.hom.app (op (U i)) _) = N.obj.map (homOfLE hV).op 0
  rw [← NatTrans.naturality_apply, ← hη, map_zero]
  exact congrArg (fun f : K.X 2 ⟶ N ↦ f.hom.app (op V) η) he

/-- The vanishing criterion on the original nonnegative sheaf complex retains
the target and differential of the literal residue chart. -/
theorem annihilator_of_properClassNat_zero (L : CochainComplex (AbSheaf X) ℕ)
    (hc : (⨆ i, U i) = ⊤) (s : ResiduesNat U L)
    (hz : properClassNat U L hc s = 0) (i : ι) {N : AbSheaf X} (e : L.X 3 ⟶ N)
    (he : L.d 2 3 ≫ e = 0) :
    e.hom.app (op (U i))
      ((L.X 3).obj.map (FreeCech.vertexInclusion U i).op (s.vertices (fun _ ↦ i))) = 0 := by
  let e' : (integerComplex L).X 3 ⟶ N := (inDegree L 3).hom ≫ e
  have he' : (integerComplex L).d 2 3 ≫ e' = 0 := by
    rw [L.extend_d_eq ComplexShape.embeddingUpNat (i := 2) (j := 3) rfl rfl]
    simp [e', inDegree, Category.assoc, he]
  rw [← properClassNat_vertex_section U L s i]
  change e'.hom.app _ (freeOpenSections _ _ _) = 0
  rw [properClass_vertex_section]
  exact annihilator_of_properClass_zero hc (s.toResidues U L) hz i e' he'

/-- A residue whose proper class vanishes on W is killed by every annihilator
on any smaller open lying in both W and the chosen chart. -/
theorem annihilator_of_properClass_restrict_zero (hc : (⨆ i, U i) = ⊤) (s : Residues U K)
    (W : Opens X) (hz : DerivedCategory.Q.map
      ((single (AbSheaf X) (ComplexShape.up ℤ) (3 : ℤ)).map
        (CycleQ2InjectiveCech.freeOpenMap (show W ≤ ⊤ from le_top))) ≫ properClass hc s = 0)
    (i : ι) (V : Opens X) (hV : V ≤ U i ⊓ W) {N : AbSheaf X} (e : K.X 3 ⟶ N)
    (he : K.d 2 3 ≫ e = 0) :
    e.hom.app (op V) ((K.X 3).obj.map (homOfLE (hV.trans inf_le_left)).op
      ((K.X 3).obj.map (FreeCech.vertexInclusion U i).op (s.vertices (fun _ ↦ i)))) = 0 := by
  let A := single (AbSheaf X) (ComplexShape.up ℤ) (3 : ℤ)
  let F := (CycleQ2MayerVietorisRestriction.freeOpenSheaf (X := X)) ⋙ A ⋙ DerivedCategory.Q
  let hᵢ : V ≤ U i := hV.trans inf_le_left
  let hW : V ≤ W := hV.trans inf_le_right
  let c := CechHyperRoof.vertexCocycle 3 (FreeCech.vertexSheafMap U i)
    (TotalThreeChainMap.chainMap (signed s))
  let cV := A.map (CycleQ2InjectiveCech.freeOpenMap hᵢ) ≫ c
  have hfac : F.map (homOfLE hᵢ) ≫ F.map (homOfLE (show U i ≤ ⊤ from le_top)) =
      F.map (homOfLE hW) ≫ F.map (homOfLE (show W ≤ ⊤ from le_top)) := by
    rw [← F.map_comp, ← F.map_comp] <;> congr 1
  have hzero : DerivedCategory.Q.map cV = 0 := by
    change DerivedCategory.Q.map (A.map (CycleQ2InjectiveCech.freeOpenMap hᵢ) ≫ c) = 0
    rw [Functor.map_comp]
    change F.map (homOfLE hᵢ) ≫ DerivedCategory.Q.map c = 0
    rw [← properClass_restrict hc s i]
    change F.map (homOfLE hᵢ) ≫ F.map (homOfLE (show U i ≤ ⊤ from le_top)) ≫ properClass hc s = 0
    rw [← Category.assoc, hfac, Category.assoc]
    change F.map (homOfLE hW) ≫ (DerivedCategory.Q.map (A.map
      (CycleQ2InjectiveCech.freeOpenMap (show W ≤ ⊤ from le_top))) ≫ properClass hc s) = 0
    rw [hz, comp_zero]
  have h := NeighborhoodPrimitive.annihilator_of_derived_zero K 3 V cV hzero e he
  have hsec := NeighborhoodPrimitive.sectionOf_restrict K 3 hᵢ c
  change NeighborhoodPrimitive.sectionOf K 3 V cV =
    (K.X 3).obj.map (homOfLE hᵢ).op (NeighborhoodPrimitive.sectionOf K 3 (U i) c) at hsec
  rw [hsec] at h
  change e.hom.app (op V) ((K.X 3).obj.map (homOfLE hᵢ).op
    (freeOpenSections _ _ _)) = 0 at h
  rw [properClass_vertex_section] at h
  exact h

/-- The localized annihilator criterion, evaluated in the original natural-degree
complex before extension by zero. -/
theorem annihilator_of_properClassNat_restrict_zero (L : CochainComplex (AbSheaf X) ℕ)
    (hc : (⨆ i, U i) = ⊤) (s : ResiduesNat U L) (W : Opens X)
    (hz : DerivedCategory.Q.map ((single (AbSheaf X) (ComplexShape.up ℤ) (3 : ℤ)).map
      (CycleQ2InjectiveCech.freeOpenMap (show W ≤ ⊤ from le_top))) ≫ properClassNat U L hc s = 0)
    (i : ι) (V : Opens X) (hV : V ≤ U i ⊓ W) {N : AbSheaf X} (e : L.X 3 ⟶ N)
    (he : L.d 2 3 ≫ e = 0) :
    e.hom.app (op V) ((L.X 3).obj.map (homOfLE (hV.trans inf_le_left)).op
      ((L.X 3).obj.map (FreeCech.vertexInclusion U i).op (s.vertices (fun _ ↦ i)))) = 0 := by
  let e' : (integerComplex L).X 3 ⟶ N := (inDegree L 3).hom ≫ e
  have he' : (integerComplex L).d 2 3 ≫ e' = 0 := by
    rw [L.extend_d_eq ComplexShape.embeddingUpNat (i := 2) (j := 3) rfl rfl]
    simp [e', inDegree, Category.assoc, he]
  rw [← properClassNat_vertex_section U L s i, ← NatTrans.naturality_apply (inDegree L 3).hom.hom]
  change e'.hom.app (op V) (((integerComplex L).X 3).obj.map
    (homOfLE (hV.trans inf_le_left)).op (freeOpenSections _ _ _)) = 0
  rw [properClass_vertex_section]
  exact annihilator_of_properClass_restrict_zero hc (s.toResidues U L) W hz i V hV e' he'

end CycleQ2.GlobalResidueClass
end
#print axioms CycleQ2.GlobalResidueClass.localPrimitive_of_properClass_zero
#print axioms CycleQ2.GlobalResidueClass.stalkPrimitive_of_properClass_zero
#print axioms CycleQ2.GlobalResidueClass.annihilator_of_properClassNat_zero
#print axioms CycleQ2.GlobalResidueClass.annihilator_of_properClassNat_restrict_zero
