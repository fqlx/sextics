import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel

/-!
# Degree-three cohomology of the Čech–de Rham total complex

Use the Čech degree first. With total differential δ + (−1)^p d, all four
summands in total degree three and all three boundary terms in total degree
two occur in the quotient. Projecting to a vertex therefore takes every
total boundary to an ordinary exterior derivative.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2CechDeRhamTotalThree

universe u

/-- An additive double cochain complex with commuting squares. Its total
differential acquires the Čech sign below. -/
structure Double where
  X : ℕ → ℕ → AddCommGrpCat.{u}
  h : ∀ p q, X p q →+ X (p+1) q
  v : ∀ p q, X p q →+ X p (q+1)
  hh : ∀ p q a, h (p+1) q (h p q a) = 0
  vv : ∀ p q a, v p (q+1) (v p q a) = 0
  hv : ∀ p q a, h p (q+1) (v p q a) = v (p+1) q (h p q a)

variable (B : Double.{u})
abbrev Two := B.X 0 2 × B.X 1 1 × B.X 2 0
abbrev Three := B.X 0 3 × B.X 1 2 × B.X 2 1 × B.X 3 0
abbrev Four := B.X 0 4 × B.X 1 3 × B.X 2 2 × B.X 3 1 × B.X 4 0

def d2 : Two B →+ Three B where
  toFun z := (B.v 0 2 z.1, B.h 0 2 z.1 - B.v 1 1 z.2.1,
    B.h 1 1 z.2.1 + B.v 2 0 z.2.2, B.h 2 0 z.2.2)
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
    exact Prod.ext rfl (Prod.ext (by dsimp; abel) (Prod.ext (by dsimp; abel) rfl))

def d3 : Three B →+ Four B where
  toFun z := (B.v 0 3 z.1, B.h 0 3 z.1 - B.v 1 2 z.2.1,
    B.h 1 2 z.2.1 + B.v 2 1 z.2.2.1, B.h 2 1 z.2.2.1 - B.v 3 0 z.2.2.2,
    B.h 3 0 z.2.2.2)
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
    exact Prod.ext rfl (Prod.ext (by dsimp; abel) (Prod.ext (by dsimp; abel) (Prod.ext (by dsimp; abel) rfl)))

theorem d3_d2 (x : Two B) : d3 B (d2 B x) = 0 := by
  apply Prod.ext
  · exact B.vv 0 2 _
  apply Prod.ext
  · change B.h 0 3 (B.v 0 2 _) - B.v 1 2 (B.h 0 2 _ - B.v 1 1 _) = 0
    rw [B.hv, map_sub, B.vv]; abel
  apply Prod.ext
  · change B.h 1 2 (B.h 0 2 _ - B.v 1 1 _) + B.v 2 1 (B.h 1 1 _ + B.v 2 0 _) = 0
    rw [map_sub, B.hh, B.hv, map_add, B.vv]; abel
  apply Prod.ext
  · change B.h 2 1 (B.h 1 1 _ + B.v 2 0 _) - B.v 3 0 (B.h 2 0 _) = 0
    rw [map_add, B.hh, B.hv]; abel
  · exact B.hh 2 0 _

abbrev Cycles := (d3 B).ker

def boundaries : Two B →+ Cycles B :=
  (d2 B).codRestrict _ (d3_d2 B)

abbrev HThree := (Cycles B) ⧸ (boundaries B).range

def classOf : Cycles B →+ HThree B := QuotientAddGroup.mk' _

/-- Poincaré residue anticommutes with the exterior derivative and commutes
with restriction. The alternating signs put the three residue terms together
in the ordinary total complex. -/
def residueCycle (a : B.X 0 3) (b : B.X 1 2) (c : B.X 2 1)
    (ha : B.v 0 3 a = 0) (hb : B.h 0 3 a = -(B.v 1 2 b))
    (hc : B.h 1 2 b = B.v 2 1 c) (hd : B.h 2 1 c = 0) : Cycles B := by
  refine ⟨(a,-b,c,0),?_⟩
  change (B.v 0 3 a,B.h 0 3 a - B.v 1 2 (-b),B.h 1 2 (-b) + B.v 2 1 c,
    B.h 2 1 c - B.v 3 0 0,B.h 3 0 0) = 0
  simp [ha,hb,hc,hd]

theorem classOf_eq_zero (z : Cycles B) : classOf B z = 0 ↔ ∃ x : Two B, d2 B x = z.1 := by
  change QuotientAddGroup.mk z = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨fun ⟨x,hx⟩ => ⟨x,congrArg Subtype.val hx⟩,
    fun ⟨x,hx⟩ => ⟨x,Subtype.ext hx⟩⟩

/-- The actual vertex primitive of a total boundary is its bidegree (0,2)
component. This statement retains no Hodge filtration truncation. -/
theorem vertex_exact (z : Cycles B) (hz : classOf B z = 0) :
    ∃ a : B.X 0 2, B.v 0 2 a = z.1.1 := by
  obtain ⟨x,hx⟩ := (classOf_eq_zero B z).1 hz
  exact ⟨x.1,congrArg Prod.fst hx⟩

variable {Q : Type*} [AddCommGroup Q]

/-- Every evaluation of vertex three-forms that kills local differentials
induces a homomorphism on full Čech–de Rham degree-three cohomology. -/
def vertexMap (ev : B.X 0 3 →+ Q) (hev : ∀ a, ev (B.v 0 2 a) = 0) : HThree B →+ Q :=
  let f : Cycles B →+ Q := ev.comp ((AddMonoidHom.fst _ _).comp (Cycles B).subtype)
  QuotientAddGroup.lift _ f (by
    rintro y ⟨x,rfl⟩
    exact hev x.1)

@[simp] theorem vertexMap_classOf (ev : B.X 0 3 →+ Q) (hev : ∀ a, ev (B.v 0 2 a) = 0)
    (z : Cycles B) : vertexMap B ev hev (classOf B z) = ev z.1.1 := rfl

end CycleQ2CechDeRhamTotalThree
end
#print axioms CycleQ2CechDeRhamTotalThree.vertex_exact
#print axioms CycleQ2CechDeRhamTotalThree.vertexMap_classOf
