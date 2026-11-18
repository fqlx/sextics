import Proposal.GeometricThreeOpenH2Surjectivity
import Proposal.GeometricAffineHThree
import Proposal.GeometricAffineHTwo
import Proposal.GeometricLiteralAmbientAffineCohomology
import Proposal.GeometricHodgeThreefoldProper

/-!
# Derived degree three on the four affine charts of the marked threefold

The four-chart comparison uses three Mayer–Vietoris connecting maps. Its
kernel is the alternating sum of actual triple restrictions. On the marked
threefold the affine charts and pair intersections supply every vanishing
needed to identify this kernel.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2FourOpenHThree

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2MayerVietorisRestriction CycleQ2ThreeOpenCechH2 CycleQ2GeometricConeCech.HZero

variable {X : TopCat.{0}}

private abbrev Square := (Opens.grothendieckTopology X).MayerVietorisSquare

private def squareMap (S T : Square (X := X)) (h₁ : S.X₁ ≤ T.X₁) (h₂ : S.X₂ ≤ T.X₂)
    (h₃ : S.X₃ ≤ T.X₃) (h₄ : S.X₄ ≤ T.X₄) : S.shortComplex ⟶ T.shortComplex where
  τ₁ := (freeOpenSheaf (X := X)).map (homOfLE h₁)
  τ₂ := biprod.map ((freeOpenSheaf (X := X)).map (homOfLE h₂))
    ((freeOpenSheaf (X := X)).map (homOfLE h₃))
  τ₃ := (freeOpenSheaf (X := X)).map (homOfLE h₄)
  comm₁₂ := by
    let K := freeOpenSheaf (X := X)
    change K.map _ ≫ biprod.lift (K.map _) (-(K.map _)) =
      biprod.lift (K.map _) (-(K.map _)) ≫ biprod.map (K.map _) (K.map _)
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc, ← Functor.map_comp]
      congr 1
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.comp_neg,
        Preadditive.neg_comp, ← Functor.map_comp]
      congr 2
  comm₂₃ := by
    let K := freeOpenSheaf (X := X)
    change biprod.map (K.map _) (K.map _) ≫ biprod.desc (K.map _) (K.map _) =
      biprod.desc (K.map _) (K.map _) ≫ K.map _
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc,
        biprod.inl_desc_assoc, ← Functor.map_comp]
      congr 1
    · simp only [biprod.inr_map_assoc, biprod.inr_desc,
        biprod.inr_desc_assoc, ← Functor.map_comp]
      congr 1

variable [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})

private theorem delta_map (S T : Square (X := X)) (h₁ : S.X₁ ≤ T.X₁) (h₂ : S.X₂ ≤ T.X₂)
    (h₃ : S.X₃ ≤ T.X₃) (h₄ : S.X₄ ≤ T.X₄) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : F.H' n₀ T.X₁) :
    (F.cohomologyPresheaf n₁).map (homOfLE h₄).op (T.δ F n₀ n₁ h x) =
      S.δ F n₀ n₁ h ((F.cohomologyPresheaf n₀).map (homOfLE h₁).op x) := by
  let f := squareMap S T h₁ h₂ h₃ h₄
  let h' : 1 + n₀ = n₁ := (Nat.add_comm 1 n₀).trans h
  change (Ext.mk₀ f.τ₃).comp (T.shortComplex_shortExact.extClass.comp x h')
      (zero_add n₁) =
    S.shortComplex_shortExact.extClass.comp
      ((Ext.mk₀ f.τ₁).comp x (zero_add n₀)) h'
  rw [← Ext.comp_assoc_of_second_deg_zero]
  rw [ShortComplex.ShortExact.extClass_naturality S.shortComplex_shortExact
    T.shortComplex_shortExact f]
  exact (Ext.comp_assoc (Ext.mk₀ f.τ₃) T.shortComplex_shortExact.extClass x
    (zero_add 1) h' (by omega)).symm

variable (U V W Z : Opens X)

abbrev QuadOpen := TripleOpen (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)

def Face : Fin 4 → Opens X
  | 0 => (V ⊓ Z) ⊓ (W ⊓ Z)
  | 1 => (U ⊓ Z) ⊓ (W ⊓ Z)
  | 2 => (U ⊓ Z) ⊓ (V ⊓ Z)
  | 3 => TripleOpen U V W

abbrev Sections (O : Opens X) := F.obj.obj (op O)
abbrev Faces := (i : Fin 4) → Sections F (Face U V W Z i)

omit [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
private theorem quad_le : QuadOpen U V W Z ≤ TripleOpen U V W :=
  inf_le_inf (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_left inf_le_left)

private def restrictLastFace : Sections F (TripleOpen U V W) →+ Sections F (QuadOpen U V W Z) :=
  (F.obj.map (homOfLE (quad_le U V W Z)).op).hom

/-- The four triple restrictions ordered by omitted coordinate, with signs +, −, +, −. -/
def boundary : Faces F U V W Z →+ Sections F (QuadOpen U V W Z) where
  toFun p := CycleQ2ThreeOpenSectionH2.boundary F (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) (p 2, p 1, p 0) -
    restrictLastFace F U V W Z (p 3)
  map_zero' := by simp [CycleQ2ThreeOpenSectionH2.boundary]
  map_add' p q := by
    change CycleQ2ThreeOpenSectionH2.boundary F _ _ _ ((p 2, p 1, p 0) + (q 2, q 1, q 0)) -
      restrictLastFace F U V W Z (p 3 + q 3) = _
    rw [map_add, map_add]
    abel

omit [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
theorem quad_le_face : ∀ i : Fin 4, QuadOpen U V W Z ≤ Face U V W Z i
  | 0 => inf_le_right
  | 1 => inf_le_left
  | 2 => inf_le_inf inf_le_left inf_le_left
  | 3 => quad_le U V W Z

def restrictFace (i : Fin 4) : Sections F (Face U V W Z i) →+ Sections F (QuadOpen U V W Z) :=
  (F.obj.map (homOfLE (quad_le_face U V W Z i)).op).hom

theorem boundary_apply (p : Faces F U V W Z) : boundary F U V W Z p =
    restrictFace F U V W Z 0 (p 0) - restrictFace F U V W Z 1 (p 1) +
    restrictFace F U V W Z 2 (p 2) - restrictFace F U V W Z 3 (p 3) := rfl

private def outer : Square (X := X) :=
  Opens.mayerVietorisSquare'
    { X₁ := ((U ⊓ Z) ⊔ (V ⊓ Z)) ⊔ (W ⊓ Z)
      X₂ := (U ⊔ V) ⊔ W
      X₃ := Z
      X₄ := ((U ⊔ V) ⊔ W) ⊔ Z
      f₁₂ := homOfLE (sup_le_sup (sup_le_sup inf_le_left inf_le_left) inf_le_left)
      f₁₃ := homOfLE (sup_le (sup_le inf_le_right inf_le_right) inf_le_right)
      f₂₄ := homOfLE le_sup_left
      f₃₄ := homOfLE le_sup_right
      fac := Subsingleton.elim _ _ }
    rfl (by simp only [inf_sup_right])

/-- The actual Mayer–Vietoris class of a section on the quadruple overlap. -/
def connecting : Sections F (QuadOpen U V W Z) →+ F.H' 3 (((U ⊔ V) ⊔ W) ⊔ Z) :=
  ((outer U V W Z).δ F 2 3 rfl).hom.comp
    (CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ Z) (V ⊓ Z) (W ⊓ Z))

private theorem connecting_restriction (a : Sections F (TripleOpen U V W)) :
    (F.cohomologyPresheaf 2).map (outer U V W Z).f₁₂.op
      (CycleQ2ThreeOpenSectionH2.connecting F U V W a) =
    CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
      (restrictLastFace F U V W Z a) := by
  let S := outerSquare (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
  let T := outerSquare U V W
  let hA : (U ⊓ Z) ⊓ (W ⊓ Z) ≤ U ⊓ W := inf_le_inf inf_le_left inf_le_left
  let hB : (V ⊓ Z) ⊓ (W ⊓ Z) ≤ V ⊓ W := inf_le_inf inf_le_left inf_le_left
  let s := (sectionsEquiv F (TripleOpen U V W)).symm a
  let y := (Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)).δ F 0 1 rfl s
  change (F.cohomologyPresheaf 2).map (outer U V W Z).f₁₂.op (T.δ F 1 2 rfl y) = S.δ F 1 2 rfl _
  refine (delta_map F S T (sup_le_sup hA hB) (sup_le_sup inf_le_left inf_le_left) inf_le_left
    (sup_le_sup (sup_le_sup inf_le_left inf_le_left) inf_le_left) 1 2 rfl y).trans ?_
  apply congrArg (S.δ F 1 2 rfl)
  refine (delta_restriction F hA hB 0 1 rfl s).trans ?_
  apply congrArg ((Opens.mayerVietorisSquare _ _).δ F 0 1 rfl)
  apply (sectionsEquiv F _).injective
  refine (sectionsEquiv_naturality F (homOfLE (inf_le_inf hA hB)) s).trans ?_
  change F.obj.map _ (sectionsEquiv F _ s) = sectionsEquiv F _
    ((sectionsEquiv F _).symm (restrictLastFace F U V W Z a))
  rw [show sectionsEquiv F _ s = a from (sectionsEquiv F _).apply_symm_apply a,
    AddEquiv.apply_symm_apply]
  rfl

/-- The four signed triple restrictions give the zero derived class. -/
theorem connecting_boundary (p : Faces F U V W Z) :
    connecting F U V W Z (boundary F U V W Z p) = 0 := by
  let S := outer U V W Z
  let C := CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
  change S.δ F 2 3 rfl (C (CycleQ2ThreeOpenSectionH2.boundary F _ _ _ (p 2, p 1, p 0) -
    restrictLastFace F U V W Z (p 3))) = 0
  rw [map_sub, show C (CycleQ2ThreeOpenSectionH2.boundary F _ _ _ (p 2, p 1, p 0)) = 0 from
    CycleQ2ThreeOpenSectionH2.connecting_boundary F _ _ _ _, zero_sub, map_neg,
    show C (restrictLastFace F U V W Z (p 3)) = _ from (connecting_restriction F U V W Z (p 3)).symm,
    delta_left_zero, neg_zero]

section Injection

variable [Subsingleton (F.H' 2 U)] [Subsingleton (F.H' 2 V)]
  [Subsingleton (F.H' 2 W)] [Subsingleton (F.H' 2 Z)]
  [Subsingleton (F.H' 1 (U ⊓ V))] [Subsingleton (F.H' 1 (U ⊓ W))]
  [Subsingleton (F.H' 1 (V ⊓ W))] [Subsingleton (F.H' 1 (U ⊓ Z))]
  [Subsingleton (F.H' 1 (V ⊓ Z))] [Subsingleton (F.H' 1 (W ⊓ Z))]

theorem connecting_eq_zero_iff (x : Sections F (QuadOpen U V W Z)) :
    connecting F U V W Z x = 0 ↔ ∃ p : Faces F U V W Z, boundary F U V W Z p = x := by
  constructor
  · let S := outer U V W Z
    let C := CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
    intro hx
    obtain ⟨a,b,hab⟩ := (delta_eq_zero_iff F S 2 3 rfl (C x)).mp hx
    have hb : b = 0 := Subsingleton.elim (α := F.H' 2 Z) _ _
    obtain ⟨v,hv⟩ := CycleQ2ThreeOpenH2Surjectivity.connecting_surjective F U V W a
    have hcv : C (restrictLastFace F U V W Z v) = C x := by
      rw [show C (restrictLastFace F U V W Z v) = _ from (connecting_restriction F U V W Z v).symm, hv]
      simpa only [hb, map_zero, sub_zero] using hab
    have hzero : C (x - restrictLastFace F U V W Z v) = 0 := by
      rw [map_sub, hcv, sub_self]
    obtain ⟨a',b',c',h⟩ := (CycleQ2ThreeOpenSectionH2.connecting_eq_zero_iff F
      (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) _).mp hzero
    let p : Faces F U V W Z
      | 0 => c'
      | 1 => b'
      | 2 => a'
      | 3 => -v
    refine ⟨p, ?_⟩
    change CycleQ2ThreeOpenSectionH2.boundary F _ _ _ (a',b',c') -
      restrictLastFace F U V W Z (-v) = x
    rw [h, map_neg]
    abel
  · rintro ⟨p, rfl⟩
    exact connecting_boundary F U V W Z p

abbrev CechH3 := Sections F (QuadOpen U V W Z) ⧸ (boundary F U V W Z).range

theorem connecting_ker : (connecting F U V W Z).ker = (boundary F U V W Z).range := by
  ext x
  exact connecting_eq_zero_iff F U V W Z x

def toSheafH3 : CechH3 F U V W Z →+ F.H' 3 (((U ⊔ V) ⊔ W) ⊔ Z) :=
  QuotientAddGroup.lift _ (connecting F U V W Z) (connecting_ker F U V W Z).symm.le

theorem toSheafH3_injective : Function.Injective (toSheafH3 F U V W Z) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2 (connecting_ker F U V W Z).symm

end Injection

private theorem delta_surj (S : Square (X := X)) (n₀ n₁ : ℕ) (hn : n₀+1 = n₁)
    (h₂ : Subsingleton (F.H' n₁ S.X₂)) (h₃ : Subsingleton (F.H' n₁ S.X₃)) :
    Function.Surjective (S.δ F n₀ n₁ hn) := by
  intro y
  have hnext : S.toBiprod F n₁ y = 0 := by
    rw [S.toBiprod_apply]
    have hz : ((F.cohomologyPresheaf n₁).map S.f₂₄.op y,
        (F.cohomologyPresheaf n₁).map S.f₃₄.op y) = (0,0) :=
      Prod.ext (h₂.elim _ _) (h₃.elim _ _)
    rw [hz]
    exact map_zero _
  exact (ShortComplex.ab_exact_iff _).mp ((S.sequence_exact F n₀ n₁ hn).exact 2) y hnext

private theorem union_vanish (S : Square (X := X)) (n₀ n₁ : ℕ) (hn : n₀+1 = n₁)
    (h₁ : Subsingleton (F.H' n₀ S.X₁)) (h₂ : Subsingleton (F.H' n₁ S.X₂))
    (h₃ : Subsingleton (F.H' n₁ S.X₃)) : Subsingleton (F.H' n₁ S.X₄) := by
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨x,rfl⟩ := delta_surj F S n₀ n₁ hn h₂ h₃ y
  rw [h₁.elim x 0, map_zero]

section Surjection

variable [hU : Subsingleton (F.H' 3 U)] [hV : Subsingleton (F.H' 3 V)]
  [hW : Subsingleton (F.H' 3 W)] [hZ : Subsingleton (F.H' 3 Z)]
  [hUV : Subsingleton (F.H' 2 (U ⊓ V))] [hUW : Subsingleton (F.H' 2 (U ⊓ W))]
  [hVW : Subsingleton (F.H' 2 (V ⊓ W))] [Subsingleton (F.H' 2 (U ⊓ Z))]
  [Subsingleton (F.H' 2 (V ⊓ Z))] [Subsingleton (F.H' 2 (W ⊓ Z))]
  [hUVW : Subsingleton (F.H' 1 (Face U V W Z 3))] [Subsingleton (F.H' 1 (Face U V W Z 2))]
  [Subsingleton (F.H' 1 (Face U V W Z 1))] [Subsingleton (F.H' 1 (Face U V W Z 0))]

/-- Four-open surjectivity uses the successive vanishings in degrees 3, 2,
and 1 on the vertices, edges, and triangles. -/
theorem connecting_surjective : Function.Surjective (connecting F U V W Z) := by
  have huv : Subsingleton (F.H' 3 (U ⊔ V)) :=
    union_vanish F (Opens.mayerVietorisSquare U V) 2 3 rfl hUV hU hV
  have huvW : Subsingleton (F.H' 2 ((U ⊓ W) ⊔ (V ⊓ W))) :=
    union_vanish F (Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)) 1 2 rfl hUVW hUW hVW
  have huvw : Subsingleton (F.H' 3 ((U ⊔ V) ⊔ W)) :=
    union_vanish F (outerSquare U V W) 2 3 rfl huvW huv hW
  let : Subsingleton (F.H' 1 ((U ⊓ Z) ⊓ (V ⊓ Z))) :=
    inferInstanceAs (Subsingleton (F.H' 1 (Face U V W Z 2)))
  let : Subsingleton (F.H' 1 ((U ⊓ Z) ⊓ (W ⊓ Z))) :=
    inferInstanceAs (Subsingleton (F.H' 1 (Face U V W Z 1)))
  let : Subsingleton (F.H' 1 ((V ⊓ Z) ⊓ (W ⊓ Z))) :=
    inferInstanceAs (Subsingleton (F.H' 1 (Face U V W Z 0)))
  exact (delta_surj F (outer U V W Z) 2 3 rfl huvw hZ).comp
    (CycleQ2ThreeOpenH2Surjectivity.connecting_surjective F (U ⊓ Z) (V ⊓ Z) (W ⊓ Z))

end Surjection

/-- Transport the actual connecting map along a four-open cover equality. -/
def connectingAtTop (hc : ((U ⊔ V) ⊔ W) ⊔ Z = ⊤) :
    Sections F (QuadOpen U V W Z) →+ F.H' 3 ⊤ :=
  (((F.cohomologyPresheaf 3).mapIso (eqToIso hc.symm).op).addCommGroupIsoToAddEquiv).toAddMonoidHom.comp
    (connecting F U V W Z)

variable (D : Fin 4 → Opens X)

omit [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
theorem quad_eq_inf : QuadOpen (D 0) (D 1) (D 2) (D 3) = Finset.univ.inf D := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [QuadOpen, TripleOpen, inf_left_comm, inf_comm]

omit [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
theorem face_eq_inf (i : Fin 4) : Face (D 0) (D 1) (D 2) (D 3) i = (Finset.univ.erase i).inf D := by
  fin_cases i
  · change Face (D 0) (D 1) (D 2) (D 3) 0 = (Finset.univ.erase (0 : Fin 4)).inf D
    rw [show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    simp [Face, inf_assoc, inf_left_comm, inf_comm]
  · change Face (D 0) (D 1) (D 2) (D 3) 1 = (Finset.univ.erase (1 : Fin 4)).inf D
    rw [show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    simp [Face, inf_assoc, inf_left_comm, inf_comm]
  · change Face (D 0) (D 1) (D 2) (D 3) 2 = (Finset.univ.erase (2 : Fin 4)).inf D
    rw [show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
    simp [Face, inf_assoc, inf_left_comm, inf_comm]
  · change Face (D 0) (D 1) (D 2) (D 3) 3 = (Finset.univ.erase (3 : Fin 4)).inf D
    rw [show Finset.univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
    simp [Face, TripleOpen, inf_assoc, inf_left_comm, inf_comm]

omit [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
theorem four_cover (h : (⨆ i, D i) = ⊤) : ((D 0 ⊔ D 1) ⊔ D 2) ⊔ D 3 = ⊤ := by
  rw [← h]
  apply le_antisymm
  · exact sup_le (sup_le (sup_le (le_iSup _ 0) (le_iSup _ 1)) (le_iSup _ 2)) (le_iSup _ 3)
  · apply iSup_le
    intro i
    fin_cases i
    · exact (le_sup_left.trans le_sup_left).trans le_sup_left
    · exact (le_sup_right.trans le_sup_left).trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right

theorem connectingAtTop_kernel_of_vanishing (hc : ((D 0 ⊔ D 1) ⊔ D 2) ⊔ D 3 = ⊤)
    (hTwo : ∀ i, Subsingleton (F.H' 2 (D i)))
    (hOne : ∀ i j, i ≠ j → Subsingleton (F.H' 1 (D i ⊓ D j)))
    (x : Sections F (QuadOpen (D 0) (D 1) (D 2) (D 3))) :
    connectingAtTop F (D 0) (D 1) (D 2) (D 3) hc x = 0 ↔
      ∃ p, boundary F (D 0) (D 1) (D 2) (D 3) p = x := by
  let : Subsingleton (F.H' 2 (D 0)) := hTwo 0
  let : Subsingleton (F.H' 2 (D 1)) := hTwo 1
  let : Subsingleton (F.H' 2 (D 2)) := hTwo 2
  let : Subsingleton (F.H' 2 (D 3)) := hTwo 3
  let : Subsingleton (F.H' 1 (D 0 ⊓ D 1)) := hOne 0 1 (by decide)
  let : Subsingleton (F.H' 1 (D 0 ⊓ D 2)) := hOne 0 2 (by decide)
  let : Subsingleton (F.H' 1 (D 1 ⊓ D 2)) := hOne 1 2 (by decide)
  let : Subsingleton (F.H' 1 (D 0 ⊓ D 3)) := hOne 0 3 (by decide)
  let : Subsingleton (F.H' 1 (D 1 ⊓ D 3)) := hOne 1 3 (by decide)
  let : Subsingleton (F.H' 1 (D 2 ⊓ D 3)) := hOne 2 3 (by decide)
  let e := ((F.cohomologyPresheaf 3).mapIso (eqToIso hc.symm).op).addCommGroupIsoToAddEquiv
  change e (connecting F (D 0) (D 1) (D 2) (D 3) x) = 0 ↔ _
  rw [map_eq_zero_iff e e.injective]
  exact connecting_eq_zero_iff F _ _ _ _ x

/-- The quotient map exists for every four-open cover. -/
def toSheafH3AtTop (hc : ((U ⊔ V) ⊔ W) ⊔ Z = ⊤) : CechH3 F U V W Z →+ F.H' 3 ⊤ :=
  QuotientAddGroup.lift (boundary F U V W Z).range (connectingAtTop F U V W Z hc) (by
    rintro _ ⟨p,rfl⟩
    change ((F.cohomologyPresheaf 3).mapIso (eqToIso hc.symm).op).addCommGroupIsoToAddEquiv
      (connecting F U V W Z (boundary F U V W Z p)) = 0
    rw [connecting_boundary, map_zero])

theorem toSheafH3AtTop_injective (hc : ((D 0 ⊔ D 1) ⊔ D 2) ⊔ D 3 = ⊤)
    (hTwo : ∀ i, Subsingleton (F.H' 2 (D i)))
    (hOne : ∀ i j, i ≠ j → Subsingleton (F.H' 1 (D i ⊓ D j))) :
    Function.Injective (toSheafH3AtTop F (D 0) (D 1) (D 2) (D 3) hc) := by
  apply (QuotientAddGroup.injective_lift_iff _ _ _).2
  ext x
  exact (connectingAtTop_kernel_of_vanishing F D hc hTwo hOne x).symm

theorem connectingAtTop_surjective_of_vanishing (hc : ((D 0 ⊔ D 1) ⊔ D 2) ⊔ D 3 = ⊤)
    (h₃ : ∀ i, Subsingleton (F.H' 3 (D i)))
    (h₂ : ∀ i j, i ≠ j → Subsingleton (F.H' 2 (D i ⊓ D j)))
    (h₁ : ∀ i, Subsingleton (F.H' 1 (Face (D 0) (D 1) (D 2) (D 3) i))) :
    Function.Surjective (connectingAtTop F (D 0) (D 1) (D 2) (D 3) hc) := by
  let : Subsingleton (F.H' 3 (D 0)) := h₃ 0
  let : Subsingleton (F.H' 3 (D 1)) := h₃ 1
  let : Subsingleton (F.H' 3 (D 2)) := h₃ 2
  let : Subsingleton (F.H' 3 (D 3)) := h₃ 3
  let : Subsingleton (F.H' 2 (D 0 ⊓ D 1)) := h₂ 0 1 (by decide)
  let : Subsingleton (F.H' 2 (D 0 ⊓ D 2)) := h₂ 0 2 (by decide)
  let : Subsingleton (F.H' 2 (D 1 ⊓ D 2)) := h₂ 1 2 (by decide)
  let : Subsingleton (F.H' 2 (D 0 ⊓ D 3)) := h₂ 0 3 (by decide)
  let : Subsingleton (F.H' 2 (D 1 ⊓ D 3)) := h₂ 1 3 (by decide)
  let : Subsingleton (F.H' 2 (D 2 ⊓ D 3)) := h₂ 2 3 (by decide)
  let : Subsingleton (F.H' 1 (Face (D 0) (D 1) (D 2) (D 3) 0)) := h₁ 0
  let : Subsingleton (F.H' 1 (Face (D 0) (D 1) (D 2) (D 3) 1)) := h₁ 1
  let : Subsingleton (F.H' 1 (Face (D 0) (D 1) (D 2) (D 3) 2)) := h₁ 2
  let : Subsingleton (F.H' 1 (Face (D 0) (D 1) (D 2) (D 3) 3)) := h₁ 3
  exact (((F.cohomologyPresheaf 3).mapIso (eqToIso hc.symm).op).addCommGroupIsoToAddEquiv.surjective).comp
    (connecting_surjective F (D 0) (D 1) (D 2) (D 3))

section StructureSheaf

open AlgebraicGeometry CycleQ2GeometricProjectiveHOne

variable {T : Scheme.{0}} (D : Fin 4 → T.Opens)

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology (show TopCat from T)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The cohomology of the structure sheaf on a four-chart affine cover with affine intersections. -/
theorem structureConnecting_surjective (hc : ((D 0 ⊔ D 1) ⊔ D 2) ⊔ D 3 = ⊤)
    (hd : ∀ i, IsAffineOpen (D i))
    (hi : ∀ {U V : T.Opens}, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) :
    Function.Surjective (connectingAtTop (structureAdditiveSheaf T) (D 0) (D 1) (D 2) (D 3) hc) := by
  apply connectingAtTop_surjective_of_vanishing
  · intro i
    exact CycleQ2GeometricAffineHThree.affineOpenHThree_subsingleton (hd i)
  · intro i j _
    exact affineFrameHTwo_subsingleton (A := Γ(T, D i ⊓ D j)) (hi (hd i) (hd j)).isoSpec
      _ (Iso.refl _) (CycleQ2GeometricAffineHTwo.affine_H_two_subsingleton _)
  · intro i
    have hp (j k : Fin 4) := hi (hd j) (hd k)
    have ha : IsAffineOpen (Face (D 0) (D 1) (D 2) (D 3) i) := by
      fin_cases i
      · exact hi (hp 1 3) (hp 2 3)
      · exact hi (hp 0 3) (hp 2 3)
      · exact hi (hp 0 3) (hp 1 3)
      · exact hi (hp 0 2) (hp 1 2)
    exact affineFrameHOne_subsingleton (A := Γ(T, Face (D 0) (D 1) (D 2) (D 3) i))
      ha.isoSpec _ (Iso.refl _)

/-- Passage to the quotient preserves surjectivity of the three connecting morphisms. -/
theorem quotient_surjective_of_connecting {Y : TopCat.{0}}
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})]
    (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) (A B C E : Opens Y)
    (hc : ((A ⊔ B) ⊔ C) ⊔ E = ⊤) (h : Function.Surjective (connectingAtTop G A B C E hc)) :
    Function.Surjective (toSheafH3AtTop G A B C E hc) := by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨QuotientAddGroup.mk' _ y, hy⟩

end StructureSheaf

end CycleQ2FourOpenHThree

namespace CycleQ2LiteralFourOpenStructureHThree

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2GeometricProjectiveHOne
  CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts
  CycleQ2FourOpenHThree

abbrev T := IncidenceFiber 57
abbrev O := structureAdditiveSheaf T
abbrev D (i : Fin 4) := fixedOpen i

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology (show TopCat from T)) AddCommGrpCat.{0}) :=
  HasExt.standard _

private theorem hTwo (i : Fin 4) : Subsingleton (O.H' 2 (D i)) :=
  CycleQ2LiteralAmbientAffineCohomology.HTwo (CycleQ2LiteralAmbientAffineCohomology.fixedOpen_affine i)

private theorem hOne (i j : Fin 4) (_ : i ≠ j) : Subsingleton (O.H' 1 (D i ⊓ D j)) :=
  CycleQ2LiteralAmbientAffineCohomology.HOne (CycleQ2LiteralAmbientAffineCohomology.pair_affine i j)

theorem cover : (((D 0 ⊔ D 1) ⊔ D 2) ⊔ D 3) = ⊤ := four_cover D fixedOpen_cover

abbrev TopSection := Sections O (QuadOpen (D 0) (D 1) (D 2) (D 3))
abbrev TripleSections := Faces O (D 0) (D 1) (D 2) (D 3)
abbrev faceBoundary := boundary O (D 0) (D 1) (D 2) (D 3)

def tripleConnecting : TopSection →+ O.H' 3 ⊤ := connectingAtTop O _ _ _ _ cover

theorem tripleConnecting_eq_zero_iff (x : TopSection) :
    tripleConnecting x = 0 ↔ ∃ p : TripleSections, faceBoundary p = x := by
  exact connectingAtTop_kernel_of_vanishing O D cover hTwo hOne x

/-- The literal four-chart quotient embeds in global derived H³ of the structure sheaf. -/
abbrev quotientConnecting := toSheafH3AtTop O (D 0) (D 1) (D 2) (D 3) cover

theorem quotientConnecting_injective : Function.Injective quotientConnecting :=
  toSheafH3AtTop_injective O D cover hTwo hOne

theorem tripleConnecting_surjective : Function.Surjective tripleConnecting :=
  structureConnecting_surjective D cover
    CycleQ2LiteralAmbientAffineCohomology.fixedOpen_affine
    (fun hU hV ↦ CycleQ2LiteralAmbientAffineCohomology.inf_affine hU hV)

theorem quotientConnecting_bijective : Function.Bijective quotientConnecting :=
  ⟨quotientConnecting_injective,
    quotient_surjective_of_connecting _ _ _ _ _ _ tripleConnecting_surjective⟩

/-- The four-chart Čech quotient computes third cohomology of the fixed marked threefold. -/
def quotientEquiv : CechH3 O (D 0) (D 1) (D 2) (D 3) ≃+ O.H' 3 ⊤ :=
  AddEquiv.ofBijective quotientConnecting quotientConnecting_bijective

#print axioms quotientEquiv
#print axioms quotientConnecting_injective
#print axioms tripleConnecting_eq_zero_iff

end CycleQ2LiteralFourOpenStructureHThree

namespace CycleQ2HodgeFourOpenStructureHThree

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricHodgeThreefold CycleQ2FourOpenHThree CycleQ2GenericSexticGradient

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

abbrev O := structureAdditiveSheaf (threefold φ)
abbrev D (i : Fin 4) := coordinateOpen φ i

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology (show TopCat from threefold φ))
    AddCommGrpCat.{0}) := HasExt.standard _

private theorem vertexAffine (i : Fin 4) : IsAffineOpen (D φ i) := .of_isIso (coordinateChart φ i).hom

private theorem infAffine {U V : (threefold φ).Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  let f := toBase φ
  let : IsProper f := toBase_proper φ
  exact (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
    U (by simp) V (by simp) hU hV

abbrev TopSection := Sections (O φ) (QuadOpen (D φ 0) (D φ 1) (D φ 2) (D φ 3))
abbrev TripleSections := Faces (O φ) (D φ 0) (D φ 1) (D φ 2) (D φ 3)
abbrev faceBoundary := boundary (O φ) (D φ 0) (D φ 1) (D φ 2) (D φ 3)

def tripleConnecting (h : IsUnit (φ vertexCoefficient)) : TopSection φ →+ (O φ).H' 3 ⊤ :=
  connectingAtTop (O φ) (D φ 0) (D φ 1) (D φ 2) (D φ 3)
    (four_cover (D φ) (coordinateOpens_cover φ h))

theorem tripleConnecting_eq_zero_iff (h : IsUnit (φ vertexCoefficient)) (x : TopSection φ) :
    tripleConnecting φ h x = 0 ↔ ∃ p : TripleSections φ, faceBoundary φ p = x := by
  apply connectingAtTop_kernel_of_vanishing
  · intro i
    exact affineFrameHTwo_subsingleton (coordinateChart φ i) _ (Iso.refl _)
      (CycleQ2GeometricAffineHTwo.affine_H_two_subsingleton _)
  · intro i j _
    exact affineFrameHOne_subsingleton (A := Γ(threefold φ, D φ i ⊓ D φ j))
      (infAffine φ (vertexAffine φ i) (vertexAffine φ j)).isoSpec _ (Iso.refl _)

theorem tripleConnecting_surjective (h : IsUnit (φ vertexCoefficient)) :
    Function.Surjective (tripleConnecting φ h) :=
  structureConnecting_surjective (D φ) _ (vertexAffine φ) (fun hU hV ↦ infAffine φ hU hV)

abbrev quotientConnecting (h : IsUnit (φ vertexCoefficient)) :=
  toSheafH3AtTop (O φ) (D φ 0) (D φ 1) (D φ 2) (D φ 3) (four_cover _ (coordinateOpens_cover φ h))

theorem quotientConnecting_bijective (h : IsUnit (φ vertexCoefficient)) :
    Function.Bijective (quotientConnecting φ h) := by
  constructor
  · apply (QuotientAddGroup.injective_lift_iff _ _ _).2
    ext x
    exact (tripleConnecting_eq_zero_iff φ h x).symm
  · exact quotient_surjective_of_connecting _ _ _ _ _ _ (tripleConnecting_surjective φ h)

/-- The top coordinate Čech quotient computes the global derived group on the moving threefold. -/
def quotientEquiv (h : IsUnit (φ vertexCoefficient)) : CechH3 (O φ) (D φ 0) (D φ 1) (D φ 2) (D φ 3) ≃+
    (O φ).H' 3 ⊤ :=
  AddEquiv.ofBijective (quotientConnecting φ h) (quotientConnecting_bijective φ h)

#print axioms quotientEquiv
#print axioms tripleConnecting_eq_zero_iff

end CycleQ2HodgeFourOpenStructureHThree
end
