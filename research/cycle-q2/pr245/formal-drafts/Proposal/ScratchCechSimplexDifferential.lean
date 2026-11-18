import Proposal.ScratchCechComplexFaces
import Proposal.ScratchCechDeRhamTotalThree
import Mathlib.Tactic.NormNum

/-! A differential chosen only on the simplex intersections of the given cover
is enough to form the actual Čech double complex. Morphisms omitting one
index account for every restriction in the horizontal differential. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open CycleQ2CechDeRhamTotalThree

namespace CycleQ2.Cech

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type} (U : ι → C)
    (P : ℕ → Cᵒᵖ ⥤ AddCommGrpCat.{0})

noncomputable abbrev Sections (p q : ℕ) (x : Fin (p + 1) → ι) :=
  (P q).obj (op (intersection U x))

structure SimplexDifferential where
  d (p q : ℕ) (x : Fin (p + 1) → ι) : Sections U P p q x →+ Sections U P p (q + 1) x
  square (p q : ℕ) (x : Fin (p + 1) → ι) (a : Sections U P p q x) :
    d p (q + 1) x (d p q x a) = 0
  face (p q : ℕ) (x : Fin (p + 2) → ι) (j : Fin (p + 2))
      (a : Sections U P p q (x ∘ j.succAbove)) :
    (P (q + 1)).map (faceRestriction U x j).op (d p q (x ∘ j.succAbove) a) =
      d (p + 1) q x ((P q).map (faceRestriction U x j).op a)

variable (D : SimplexDifferential U P)

noncomputable abbrev Cochain (p q : ℕ) := ((cechComplexFunctor U).obj (P q)).X p

/-- The tuple derivatives define a homomorphism between the actual Čech groups. -/
noncomputable def vertical (p q : ℕ) : Cochain U P p q →+ Cochain U P p (q + 1) where
  toFun z := (sectionsEquiv U (P (q + 1)) p).symm
    (fun x => D.d p q x (component U (P q) x z))
  map_zero' := by
    apply (sectionsEquiv U (P (q + 1)) p).injective
    funext x
    simp
  map_add' a b := by
    apply (sectionsEquiv U (P (q + 1)) p).injective
    funext x
    simp

@[simp]
theorem component_vertical (p q : ℕ) (x : Fin (p + 1) → ι) (z : Cochain U P p q) :
    component U (P (q + 1)) x (vertical U P D p q z) =
      D.d p q x (component U (P q) x z) :=
  component_assemble U (P (q + 1)) _ x

theorem vertical_squared (p q : ℕ) (z : Cochain U P p q) :
    vertical U P D p (q + 1) (vertical U P D p q z) = 0 := by
  apply (sectionsEquiv U (P (q + 2)) p).injective
  funext x
  simp [D.square]

/-- Naturality just for omitting one index gives the Čech/exterior derivative square. -/
theorem horizontal_vertical (p q : ℕ) (z : Cochain U P p q) :
    ((cechComplexFunctor U).obj (P (q + 1))).d p (p + 1) (vertical U P D p q z) =
      vertical U P D (p + 1) q (((cechComplexFunctor U).obj (P q)).d p (p + 1) z) := by
  apply (sectionsEquiv U (P (q + 1)) (p + 1)).injective
  funext x
  simp only [sectionsEquiv_apply, horizontal_apply, component_vertical, map_sum, map_zsmul,
    D.face]

noncomputable def simplexDouble : Double.{0} where
  X := Cochain U P
  v := vertical U P D
  h p q := (((cechComplexFunctor U).obj (P q)).d p (p + 1)).hom
  vv := vertical_squared U P D
  hv := horizontal_vertical U P D
  hh p q a := CategoryTheory.congr_fun (((cechComplexFunctor U).obj (P q)).d_comp_d p (p + 1)
    (p + 2)) a

/-- The alternating coboundary on a family of sections. -/
noncomputable def tupleDelta (p q : ℕ) (a : ∀ x, Sections U P p q x)
    (x : Fin (p + 2) → ι) : Sections U P (p + 1) q x :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    (P q).map (faceRestriction U x j).op (a (x ∘ j.succAbove))

/-- The section from the `j`-th face, restricted to the full tuple intersection. -/
noncomputable abbrev tupleFace (p q : ℕ) (a : ∀ x, Sections U P p q x)
    (x : Fin (p + 2) → ι) (j : Fin (p + 2)) : Sections U P (p + 1) q x :=
  (P q).map (faceRestriction U x j).op (a (x ∘ j.succAbove))

theorem tupleDelta_zero (q : ℕ) (a : ∀ x, Sections U P 0 q x) (x : Fin 2 → ι) :
    tupleDelta U P 0 q a x = tupleFace U P 0 q a x 0 - tupleFace U P 0 q a x 1 := by
  rw [tupleDelta, Fin.sum_univ_two]
  norm_num [tupleFace, sub_eq_add_neg] <;> abel

theorem tupleDelta_one (q : ℕ) (a : ∀ x, Sections U P 1 q x) (x : Fin 3 → ι) :
    tupleDelta U P 1 q a x = tupleFace U P 1 q a x 0 - tupleFace U P 1 q a x 1 +
      tupleFace U P 1 q a x 2 := by
  rw [tupleDelta, Fin.sum_univ_three]
  norm_num [tupleFace, sub_eq_add_neg] <;> abel

theorem tupleDelta_two (q : ℕ) (a : ∀ x, Sections U P 2 q x) (x : Fin 4 → ι) :
    tupleDelta U P 2 q a x = tupleFace U P 2 q a x 0 - tupleFace U P 2 q a x 1 +
      tupleFace U P 2 q a x 2 - tupleFace U P 2 q a x 3 := by
  rw [tupleDelta, Fin.sum_univ_four]
  norm_num [tupleFace, sub_eq_add_neg] <;> abel

noncomputable abbrev assemble (p q : ℕ) (a : ∀ x, Sections U P p q x) : Cochain U P p q :=
  (sectionsEquiv U (P q) p).symm a

@[simp]
theorem component_assembleSections (p q : ℕ) (a : ∀ x, Sections U P p q x)
    (x : Fin (p + 1) → ι) : component U (P q) x (assemble U P p q a) = a x :=
  component_assemble U (P q) a x

theorem component_h_assemble (p q : ℕ) (a : ∀ x, Sections U P p q x)
    (x : Fin (p + 2) → ι) :
    component U (P q) x ((((cechComplexFunctor U).obj (P q)).d p (p + 1)) (assemble U P p q a)) =
      tupleDelta U P p q a x := by
  simp only [horizontal_apply, component_assembleSections, tupleDelta]

/-- Assemble the signed residue cocycle directly from actual simplex sections
and their pointwise compatibility equations. -/
noncomputable def simplexResidueCycle
    (a : ∀ x, Sections U P 0 3 x) (b : ∀ x, Sections U P 1 2 x)
    (c : ∀ x, Sections U P 2 1 x)
    (ha : ∀ x, D.d 0 3 x (a x) = 0)
    (hb : ∀ x, tupleDelta U P 0 3 a x = -(D.d 1 2 x (b x)))
    (hc : ∀ x, tupleDelta U P 1 2 b x = D.d 2 1 x (c x))
    (hd : ∀ x, tupleDelta U P 2 1 c x = 0) : Cycles (simplexDouble U P D) := by
  apply residueCycle (simplexDouble U P D) (assemble U P 0 3 a) (assemble U P 1 2 b)
    (assemble U P 2 1 c)
  · apply cochain_ext U (P 4) (n := 0)
    intro x
    change component U (P 4) x (vertical U P D 0 3 (assemble U P 0 3 a)) = _
    simpa only [component_vertical, component_assembleSections, component_zero] using ha x
  · apply cochain_ext U (P 3) (n := 1)
    intro x
    change component U (P 3) x (((cechComplexFunctor U).obj (P 3)).d 0 1 (assemble U P 0 3 a)) =
      component U (P 3) x (-(vertical U P D 1 2 (assemble U P 1 2 b)))
    simpa only [component_h_assemble, component_neg, component_vertical,
      component_assembleSections] using hb x
  · apply cochain_ext U (P 2) (n := 2)
    intro x
    change component U (P 2) x (((cechComplexFunctor U).obj (P 2)).d 1 2 (assemble U P 1 2 b)) =
      component U (P 2) x (vertical U P D 2 1 (assemble U P 2 1 c))
    simpa only [component_h_assemble, component_vertical, component_assembleSections] using hc x
  · apply cochain_ext U (P 1) (n := 3)
    intro x
    change component U (P 1) x (((cechComplexFunctor U).obj (P 1)).d 2 3 (assemble U P 2 1 c)) = _
    simpa only [component_h_assemble, component_zero] using hd x

/-- At the selected cover open the signed total residue recovers the actual local residue. -/
theorem simplexResidueCycle_vertex
    (a : ∀ x, Sections U P 0 3 x) (b : ∀ x, Sections U P 1 2 x)
    (c : ∀ x, Sections U P 2 1 x)
    (ha : ∀ x, D.d 0 3 x (a x) = 0)
    (hb : ∀ x, tupleDelta U P 0 3 a x = -(D.d 1 2 x (b x)))
    (hc : ∀ x, tupleDelta U P 1 2 b x = D.d 2 1 x (c x))
    (hd : ∀ x, tupleDelta U P 2 1 c x = 0) (i : ι) :
    vertex U (P 3) i (simplexResidueCycle U P D a b c ha hb hc hd).1.1 =
      (P 3).map (singletonLift U i).op (a (fun _ => i)) := by
  change vertex U (P 3) i (assemble U P 0 3 a) = _
  simp only [vertex, ConcreteCategory.comp_apply, component_assembleSections]

/-- A derivative on the chosen open compatible with its singleton intersection
computes the restriction of each total boundary. -/
theorem vertex_vertical (q : ℕ) (i : ι)
    (dᵢ : (P q).obj (op (U i)) →+ (P (q + 1)).obj (op (U i)))
    (hᵢ : ∀ a, (P (q + 1)).map (singletonLift U i).op (D.d 0 q (fun _ => i) a) =
      dᵢ ((P q).map (singletonLift U i).op a)) (z : Cochain U P 0 q) :
    vertex U (P (q + 1)) i (vertical U P D 0 q z) = dᵢ (vertex U (P q) i z) := by
  simp only [vertex, ConcreteCategory.comp_apply, component_vertical, hᵢ]

end CycleQ2.Cech

#print axioms CycleQ2.Cech.simplexDouble

#print axioms CycleQ2.Cech.simplexResidueCycle_vertex
