import Proposal.GeometricCartierDerivedClass

/-! Sections represented by the free sheaf on the tuples of a Čech cover. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped BigOperators

namespace CycleQ2.FreeCech

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)

/-- The open on which one specified tuple of charts is defined. -/
def intersection {α : Type} (a : α → ι) : Opens X := ⨅ j, U (a j)

/-- All tuples of charts whose intersection contains a test open. -/
def indexPresheaf (α : Type) : (Opens X)ᵒᵖ ⥤ Type where
  obj V := α → {i : ι // V.unop ≤ U i}
  map f := ↾fun t j => ⟨(t j).1, (leOfHom f.unop).trans (t j).2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev freePresheaf (α : Type) := indexPresheaf U α ⋙ AddCommGrpCat.free

variable {α : Type}

/-- The universal tuple on its own intersection. -/
def generator (a : α → ι) : (indexPresheaf U α).obj (op (intersection U a)) :=
  fun j => ⟨a j, iInf_le _ j⟩

def inclusion {V : (Opens X)ᵒᵖ} (t : (indexPresheaf U α).obj V) :
    V.unop ⟶ intersection U (fun j => (t j).1) :=
  homOfLE (le_iInf fun j => (t j).2)

variable (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0})

/-- Recover a family of sections by evaluating each universal generator. -/
def presheafSections (α : Type) :
    (freePresheaf U α ⟶ F) ≃+ (∀ a : α → ι, F.obj (op (intersection U a))) where
  toFun k a := k.app _ (FreeAbelianGroup.of (generator U a))
  invFun s :=
    { app V := AddCommGrpCat.ofHom (FreeAbelianGroup.lift
        fun t : (indexPresheaf U α).obj V => F.map (inclusion U t).op (s fun j => (t j).1))
      naturality V W f := by
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro t
        simp only [Functor.comp_map, AddCommGrpCat.free_map, AddCommGrpCat.hom_comp,
          AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply, AddCommGrpCat.ofHom_apply,
          FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of]
        change F.map (inclusion U ((indexPresheaf U α).map f t)).op (s fun j => (t j).1) =
          F.map f (F.map (inclusion U t).op (s fun j => (t j).1))
        rw [← ConcreteCategory.comp_apply, ← F.map_comp]
        rfl }
  left_inv k := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro t
    simp only [AddCommGrpCat.hom_ofHom, AddCommGrpCat.ofHom_apply,
      FreeAbelianGroup.lift_apply_of]
    let a : α → ι := fun j => (t j).1
    have h := congrArg
      (fun m : (freePresheaf U α).obj (op (intersection U a)) ⟶ F.obj V =>
        m (FreeAbelianGroup.of (generator U a))) (k.naturality (inclusion U t).op)
    simpa [a, generator, indexPresheaf, Functor.comp_map, AddCommGrpCat.free_map,
      AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom] using h.symm
  right_inv s := by
    funext a
    simp only [AddCommGrpCat.ofHom_apply, FreeAbelianGroup.lift_apply_of]
    change F.map (𝟙 _) (s a) = s a
    simp
  map_add' _ _ := rfl

abbrev freeSheaf (α : Type) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (freePresheaf U α)

variable (G : CycleQ2InjectiveCech.AbSheaf X)

/-- A map from the Čech chain sheaf is exactly a section on every tuple intersection. -/
def sections (α : Type) :
    (freeSheaf U α ⟶ G) ≃+ (∀ a : α → ι, G.obj.obj (op (intersection U a))) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homAddEquiv
    (freePresheaf U α) G).trans (presheafSections U G.obj α)

variable {β : Type}

/-- Reindexing a tuple, including every face and degeneracy. -/
def reindex (u : β → α) : indexPresheaf U α ⟶ indexPresheaf U β where
  app _ := ↾fun t => t ∘ u
  naturality _ _ _ := rfl

def freeReindex (u : β → α) : freePresheaf U α ⟶ freePresheaf U β :=
  Functor.whiskerRight (reindex U u) AddCommGrpCat.free

def sheafReindex (u : β → α) : freeSheaf U α ⟶ freeSheaf U β :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map (freeReindex U u)

def faceInclusion (a : α → ι) (u : β → α) :
    intersection U a ⟶ intersection U (a ∘ u) :=
  homOfLE (le_iInf fun j => iInf_le (fun l => U (a l)) (u j))

theorem presheafSections_reindex (u : β → α) (k : freePresheaf U β ⟶ F) (a : α → ι) :
    presheafSections U F α (freeReindex U u ≫ k) a =
      F.map (faceInclusion U a u).op (presheafSections U F β k (a ∘ u)) := by
  have h := congrArg
    (fun m : (freePresheaf U β).obj (op (intersection U (a ∘ u))) ⟶
      F.obj (op (intersection U a)) => m (FreeAbelianGroup.of (generator U (a ∘ u))))
    (k.naturality (faceInclusion U a u).op)
  simpa [presheafSections, freeReindex, reindex, indexPresheaf, generator,
    Functor.whiskerRight_app, AddCommGrpCat.free_map, AddCommGrpCat.hom_comp,
    AddCommGrpCat.hom_ofHom] using h

/-- Precomposing by a Čech face becomes ordinary restriction on that intersection. -/
theorem sections_reindex (u : β → α) (k : freeSheaf U β ⟶ G) (a : α → ι) :
    sections U G α (sheafReindex U u ≫ k) a =
      G.obj.map (faceInclusion U a u).op (sections U G β k (a ∘ u)) := by
  let J := Opens.grothendieckTopology X
  change presheafSections U G.obj α
    (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ G)
      ((presheafToSheaf J AddCommGrpCat).map (freeReindex U u) ≫ k)) a = _
  rw [(sheafificationAdjunction J AddCommGrpCat).homEquiv_naturality_left]
  exact presheafSections_reindex U G.obj u _ a

/-- Postcomposing the coefficient sheaf map acts componentwise on the Čech sections. -/
theorem sections_postcomp {H : CycleQ2InjectiveCech.AbSheaf X}
    (k : freeSheaf U α ⟶ G) (g : G ⟶ H) (a : α → ι) :
    sections U H α (k ≫ g) a = g.hom.app _ (sections U G α k a) := by
  let J := Opens.grothendieckTopology X
  change presheafSections U H.obj α
    (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ H) (k ≫ g)) a = _
  rw [(sheafificationAdjunction J AddCommGrpCat).homEquiv_naturality_right]
  rfl

/-- The alternating face boundary on free chains acts on tuples by the ordinary
Čech differential, with its integral signs. -/
theorem sections_boundary {n : ℕ} (k : freeSheaf U (Fin (n + 1)) ⟶ G)
    (a : Fin (n + 2) → ι) :
    sections U G _ ((∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      sheafReindex U j.succAbove) ≫ k) a =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          G.obj.map (faceInclusion U a j.succAbove).op
            (sections U G _ k (a ∘ j.succAbove)) := by
  rw [Preadditive.sum_comp, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Preadditive.zsmul_comp, map_zsmul, Pi.smul_apply, sections_reindex]

/-- Empty tuples give the terminal presheaf. -/
def unitIsoEmpty : (Functor.const (Opens X)ᵒᵖ).obj PUnit ≅ indexPresheaf U Empty :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun _ e => Empty.elim e
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun a => funext fun e => Empty.elim e })
    (fun _ => by
      apply ConcreteCategory.hom_ext
      intro t
      funext e
      exact Empty.elim e)

/-- The terminal presheaf is represented by the entire space. -/
def unitIsoTop : (Functor.const (Opens X)ᵒᵖ).obj PUnit ≅ yoneda.obj (⊤ : Opens X) :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun _ => homOfLE le_top
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun _ => Subsingleton.elim _ _ })
    (fun _ => by
      apply ConcreteCategory.hom_ext
      intro t
      exact Subsingleton.elim _ _)

abbrev freeUnitPresheaf (X : TopCat.{0}) :=
  (Functor.const (Opens X)ᵒᵖ).obj PUnit ⋙ AddCommGrpCat.free

/-- Sheafifying the constant free group on a point gives the free sheaf on the top open. -/
def freeUnitIsoTop :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (freeUnitPresheaf X) ≅ CycleQ2InjectiveCech.freeOpen (X := X) ⊤ :=
  (presheafToSheaf _ _).mapIso
    (Functor.isoWhiskerRight (unitIsoTop (X := X)) AddCommGrpCat.free)

def vertexTuple (i : ι) : yoneda.obj (U i) ⟶ indexPresheaf U (Fin 1) where
  app _ := ↾fun f _ => ⟨i, leOfHom f⟩
  naturality _ _ _ := rfl

/-- The vertex as a sheaf map from the free sheaf on its chart. -/
def vertexSheafMap (i : ι) : CycleQ2InjectiveCech.freeOpen (U i) ⟶ freeSheaf U (Fin 1) :=
  (presheafToSheaf _ _).map (Functor.whiskerRight (vertexTuple U i) AddCommGrpCat.free)

def vertexInclusion (i : ι) : U i ⟶ intersection U (fun _ : Fin 1 => i) :=
  homOfLE (le_iInf fun _ => le_rfl)

/-- Pullback to a single vertex is its evaluated section on the chosen chart. -/
theorem vertex_sections (i : ι) (k : freeSheaf U (Fin 1) ⟶ G) :
    CycleQ2InjectiveCech.freeOpenSections G (U i) (vertexSheafMap U i ≫ k) =
      G.obj.map (vertexInclusion U i).op (sections U G (Fin 1) k (fun _ => i)) := by
  let J := Opens.grothendieckTopology X
  let A := sheafificationAdjunction J AddCommGrpCat
  let t := (A.homEquiv _ G) k
  change CycleQ2GeometricConeCech.HZero.freeYonedaSections G.obj (U i)
    ((A.homEquiv _ G) ((presheafToSheaf J AddCommGrpCat).map
      (Functor.whiskerRight (vertexTuple U i) AddCommGrpCat.free) ≫ k)) = _
  rw [A.homEquiv_naturality_left]
  have h := congrArg
    (fun m : (freePresheaf U (Fin 1)).obj (op (intersection U (fun _ : Fin 1 => i))) ⟶
      G.obj.obj (op (U i)) => m (FreeAbelianGroup.of (generator U (fun _ : Fin 1 => i))))
    (t.naturality (vertexInclusion U i).op)
  change t.app _ (FreeAbelianGroup.of (fun _ : Fin 1 => (⟨i, le_rfl⟩ : {j // U i ≤ U j}))) =
    G.obj.map _ (t.app _ (FreeAbelianGroup.of _))
  simpa [generator, indexPresheaf, Functor.comp_map, AddCommGrpCat.free_map,
    AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom] using h

def toUnit (α : Type) : indexPresheaf U α ⟶ (Functor.const (Opens X)ᵒᵖ).obj PUnit where
  app _ := ↾fun _ => PUnit.unit
  naturality _ _ _ := rfl

def augmentation (α : Type) : freeSheaf U α ⟶
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (freeUnitPresheaf X) :=
  (presheafToSheaf _ _).map (Functor.whiskerRight (toUnit U α) AddCommGrpCat.free)

/-- Augmenting a prescribed vertex is the map induced by its inclusion into the space. -/
theorem vertex_augmentation (i : ι) :
    vertexSheafMap U i ≫ augmentation U (Fin 1) ≫ (freeUnitIsoTop (X := X)).hom =
      CycleQ2InjectiveCech.freeOpenMap (show U i ≤ ⊤ from le_top) := by
  let J := Opens.grothendieckTopology X
  let L := presheafToSheaf J AddCommGrpCat
  change L.map _ ≫ L.map _ ≫ L.map _ = L.map _
  rw [← L.map_comp, ← L.map_comp]
  apply congrArg L.map
  ext V : 1
  change AddCommGrpCat.free.map _ ≫ AddCommGrpCat.free.map _ ≫
    AddCommGrpCat.free.map _ = AddCommGrpCat.free.map _
  rw [← AddCommGrpCat.free.map_comp, ← AddCommGrpCat.free.map_comp]
  apply congrArg AddCommGrpCat.free.map
  apply ConcreteCategory.hom_ext
  intro t
  exact Subsingleton.elim _ _

end CycleQ2.FreeCech
