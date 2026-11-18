import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! Sheafification inverts a presheaf map that is bijective on a topological
basis. For a complex its units commute with the full differential. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory Opposite TopologicalSpace

namespace CycleQ2.Cech.BasisSheafification

variable {X : TopCat.{0}}
abbrev J (X : TopCat.{0}) := Opens.grothendieckTopology X
abbrev Psh (X : TopCat.{0}) := (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}


theorem locallyBijective {P Q : Psh X} (f : P ⟶ Q)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hf : ∀ V ∈ B, Function.Bijective (f.app (op V))) :
    Presheaf.IsLocallyInjective (J X) f ∧ Presheaf.IsLocallySurjective (J X) f := by
  constructor
  · constructor
    intro U a b h z hz
    obtain ⟨V,hV,hzV,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hz
    let i : V ⟶ U.unop := homOfLE hVU
    refine ⟨V,i,?_,hzV⟩
    change P.map i.op a = P.map i.op b
    apply (hf V hV).injective
    simpa only [NatTrans.naturality_apply f] using congrArg (fun t => Q.map i.op t) h
  · constructor
    intro U s z hz
    obtain ⟨V,hV,hzV,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hz
    let i : V ⟶ U := homOfLE hVU
    exact ⟨V,i,(hf V hV).surjective (Q.map i.op s),hzV⟩

theorem isIso_of_basis {P Q : Psh X} (f : P ⟶ Q)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hf : ∀ V ∈ B, Function.Bijective (f.app (op V))) :
    IsIso ((presheafToSheaf (J X) AddCommGrpCat.{0}).map f) :=
  ((J X).W_iff f).mp (((J X).W_iff_isLocallyBijective f).mpr (locallyBijective f B hB hf))

def isoOfBasis {P Q : Psh X} (f : P ⟶ Q)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hf : ∀ V ∈ B, Function.Bijective (f.app (op V))) :
    (presheafToSheaf (J X) AddCommGrpCat.{0}).obj P ≅
      (presheafToSheaf (J X) AddCommGrpCat.{0}).obj Q := by
  letI := isIso_of_basis f B hB hf
  exact asIso ((presheafToSheaf (J X) AddCommGrpCat.{0}).map f)


/-- If the source already computes its associated sheaf on a given open,
the canonical map from its sections there to the target's sheafified
sections is an isomorphism. -/
theorem isIso_toSheafifiedTarget {P Q : Psh X} (f : P ⟶ Q)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hf : ∀ V ∈ B, Function.Bijective (f.app (op V)))
    (W : Opens X) (hW : IsIso ((toSheafify (J X) P).app (op W))) :
    IsIso (f.app (op W) ≫ (toSheafify (J X) Q).app (op W)) := by
  letI := hW
  letI := isIso_of_basis f B hB hf
  haveI : IsIso (sheafifyMap (J X) f) :=
    (sheafToPresheaf (J X) AddCommGrpCat.{0}).map_isIso _
  change IsIso ((f ≫ toSheafify (J X) Q).app (op W))
  rw [toSheafify_naturality]
  change IsIso ((toSheafify (J X) P).app (op W) ≫ (sheafifyMap (J X) f).app (op W))
  infer_instance

theorem isIso_unit_at_basis {P Q : Psh X} (f : P ⟶ Q)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hf : ∀ V ∈ B, Function.Bijective (f.app (op V)))
    (W : Opens X) (hW : W ∈ B) (hs : IsIso ((toSheafify (J X) P).app (op W))) :
    IsIso ((toSheafify (J X) Q).app (op W)) := by
  haveI : IsIso (f.app (op W)) := (ConcreteCategory.isIso_iff_bijective _).mpr (hf W hW)
  haveI := isIso_toSheafifiedTarget f B hB hf W hs
  exact IsIso.of_isIso_comp_left (f.app (op W)) _

def sheafComplex (X : TopCat.{0}) (K : CochainComplex (Psh X) ℕ) :
    CochainComplex (CategoryTheory.Sheaf (J X) AddCommGrpCat.{0}) ℕ :=
  ((presheafToSheaf (J X) AddCommGrpCat.{0}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The honest cochain map induced by the sheafification units. -/
def sheafComplexUnit (X : TopCat.{0}) (K : CochainComplex (Psh X) ℕ) :
    K ⟶ ((sheafToPresheaf (J X) AddCommGrpCat.{0}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (sheafComplex X K) where
  f n := toSheafify (J X) (K.X n)
  comm' i j _ := (toSheafify_naturality (J X) (K.d i j)).symm

@[simp] theorem sheafComplexUnit_f (K : CochainComplex (Psh X) ℕ) (n : ℕ) :
    (sheafComplexUnit X K).f n = toSheafify (J X) (K.X n) := rfl



/-- The analogous local criterion on the slice open site. -/
theorem over_locallyBijective (W : Opens X)
    {P Q : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{0}} (f : P ⟶ Q)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hf : ∀ V : Over W, V.left ∈ B → Function.Bijective (f.app (op V))) :
    Presheaf.IsLocallyInjective ((J X).over W) f ∧ Presheaf.IsLocallySurjective ((J X).over W) f := by
  constructor
  · constructor
    intro Y a b hab
    rw [GrothendieckTopology.mem_over_iff]
    intro z hz
    obtain ⟨V,hV,hzV,hVY⟩ := Opens.isBasis_iff_nbhd.mp hB hz
    let i : V ⟶ Y.unop.left := homOfLE hVY
    let T : Over W := Over.mk (i ≫ Y.unop.hom)
    let j : T ⟶ Y.unop := Over.homMk i
    refine ⟨V,i,(Sieve.overEquiv_iff _ _).mpr ?_,hzV⟩
    change P.map j.op a = P.map j.op b
    apply (hf T hV).injective
    simpa only [NatTrans.naturality_apply f] using congrArg (fun t => Q.map j.op t) hab
  · constructor
    intro Y s
    rw [GrothendieckTopology.mem_over_iff]
    intro z hz
    obtain ⟨V,hV,hzV,hVY⟩ := Opens.isBasis_iff_nbhd.mp hB hz
    let i : V ⟶ Y.left := homOfLE hVY
    let T : Over W := Over.mk (i ≫ Y.hom)
    let j : T ⟶ Y := Over.homMk i
    exact ⟨V,i,(Sieve.overEquiv_iff _ _).mpr ((hf T hV).surjective (Q.map j.op s)),hzV⟩

/-- A frame from a sheaf on W into its restricted presheaf, bijective on a
basis of the subopens and at W, identifies the presheaf and sheaf sections at W.
The frame may be defined only on the over-site of W. -/
theorem isIso_unit_from_over_frame (P : Psh X) (W : Opens X)
    (M : CategoryTheory.Sheaf ((J X).over W) AddCommGrpCat.{0})
    (l : M.obj ⟶ (Over.forget W).op ⋙ P) (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hl : ∀ V : Over W, V.left ∈ B → Function.Bijective (l.app (op V))) (hW : W ∈ B) :
    IsIso ((toSheafify (J X) P).app (op W)) := by
  let e := Functor.whiskerLeft (Over.forget W).op (toSheafify (J X) P)
  haveI : Presheaf.IsLocallyInjective ((J X).over W) e :=
    Presheaf.isLocallyInjective_whisker _ _ _ _
  haveI : Presheaf.IsLocallySurjective ((J X).over W) e :=
    Presheaf.isLocallySurjective_whisker _ _ _ _
  haveI := (over_locallyBijective W l B hB hl).1
  haveI := (over_locallyBijective W l B hB hl).2
  let L := (presheafToSheaf (J X) AddCommGrpCat.{0}).obj P
  let m : M ⟶ L.over W := ObjectProperty.homMk (l ≫ e)
  haveI : IsIso m :=
    (Sheaf.isLocallyBijective_iff_isIso m).mp
      ⟨Presheaf.isLocallyInjective_comp _ l e, Presheaf.isLocallySurjective_comp _ l e⟩
  let Y : Over W := Over.mk (𝟙 W)
  haveI : IsIso (l.app (op Y)) := (ConcreteCategory.isIso_iff_bijective _).mpr (hl Y hW)
  haveI : IsIso m.hom := (sheafToPresheaf _ AddCommGrpCat.{0}).map_isIso _
  haveI : IsIso (l.app (op Y) ≫ (toSheafify (J X) P).app (op W)) :=
    inferInstanceAs (IsIso (m.hom.app (op Y)))
  exact IsIso.of_isIso_comp_left (l.app (op Y)) _

abbrev underlyingComplex (L : CochainComplex (CategoryTheory.Sheaf (J X) AddCommGrpCat.{0}) ℕ) :
    CochainComplex (Psh X) ℕ :=
  ((sheafToPresheaf (J X) AddCommGrpCat.{0}).mapHomologicalComplex (ComplexShape.up ℕ)).obj L

/-- A morphism into any complex of sheaves extends along the degreewise
sheafification. This applies in particular to a complex of skyscraper sheaves
of rational forms. -/
def liftToSheafComplex {K : CochainComplex (Psh X) ℕ}
    {L : CochainComplex (CategoryTheory.Sheaf (J X) AddCommGrpCat.{0}) ℕ}
    (g : K ⟶ underlyingComplex L) : sheafComplex X K ⟶ L where
  f i := ((sheafificationAdjunction (J X) AddCommGrpCat.{0}).homEquiv (K.X i) (L.X i)).symm (g.f i)
  comm' i j _ := ((sheafificationAdjunction (J X) AddCommGrpCat.{0}).homEquiv_naturality_right_square
    (K.d i j) (g.f j) (g.f i) (L.d i j) (g.comm i j).symm).symm

@[reassoc (attr := simp)] theorem toSheafify_lift_f {K : CochainComplex (Psh X) ℕ}
    {L : CochainComplex (CategoryTheory.Sheaf (J X) AddCommGrpCat.{0}) ℕ}
    (g : K ⟶ underlyingComplex L) (q : ℕ) :
    toSheafify (J X) (K.X q) ≫ ((liftToSheafComplex g).f q).hom = g.f q :=
  toSheafify_sheafifyLift (J X) (g.f q) (L.X q).property


/-- Write a complex on the specified native sheaves themselves, transporting
the differential along degreewise identifications with their presentations. -/
def onNativeTerms {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (A : ℕ → C) (K : CochainComplex C ℕ) (e : ∀ n, A n ≅ K.X n) :
    CochainComplex C ℕ where
  X := A
  d i j := (e i).hom ≫ K.d i j ≫ (e j).inv
  shape i j hij := by simp [K.shape i j hij]
  d_comp_d' i j k _ _ := by simp [Category.assoc]

/-- Transport preserves the actual complex and hence its derived object. -/
def onNativeTermsIso {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (A : ℕ → C) (K : CochainComplex C ℕ) (e : ∀ n, A n ≅ K.X n) :
    onNativeTerms A K e ≅ K :=
  HomologicalComplex.Hom.isoOfComponents e (fun i j _ => by
    change (e i).hom ≫ K.d i j = ((e i).hom ≫ K.d i j ≫ (e j).inv) ≫ (e j).hom
    simp)

end CycleQ2.Cech.BasisSheafification
end

#print axioms CycleQ2.Cech.BasisSheafification.isoOfBasis
#print axioms CycleQ2.Cech.BasisSheafification.sheafComplexUnit
