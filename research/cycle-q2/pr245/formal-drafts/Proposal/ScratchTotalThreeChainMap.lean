import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! The signed total degree-three cocycle as a map of complexes. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2.TotalThreeChainMap

open CategoryTheory CategoryTheory.Limits

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
  {P : ChainComplex A ℕ} {K : CochainComplex A ℤ}

/-- The equations for the convention δ + (-1)^p d. -/
structure Cocycle (P : ChainComplex A ℕ) (K : CochainComplex A ℤ) where
  f0 : P.X 0 ⟶ K.X 3
  f1 : P.X 1 ⟶ K.X 2
  f2 : P.X 2 ⟶ K.X 1
  f3 : P.X 3 ⟶ K.X 0
  closed : f0 ≫ K.d 3 4 = 0
  compat1 : P.d 1 0 ≫ f0 = f1 ≫ K.d 2 3
  compat2 : P.d 2 1 ≫ f1 = -(f2 ≫ K.d 1 2)
  compat3 : P.d 3 2 ≫ f2 = f3 ≫ K.d 0 1
  compat4 : P.d 4 3 ≫ f3 = 0

abbrev embedding := ComplexShape.embeddingUpIntLE 3

def component (z : Cocycle P K) : ∀ k : ℤ, (P.extend embedding).X k ⟶ K.X k
  | .ofNat 0 => (P.extendXIso embedding (i := 3) (i' := 0) (by decide)).hom ≫ -z.f3
  | .ofNat 1 => (P.extendXIso embedding (i := 2) (i' := 1) (by decide)).hom ≫ -z.f2
  | .ofNat 2 => (P.extendXIso embedding (i := 1) (i' := 2) (by decide)).hom ≫ z.f1
  | .ofNat 3 => (P.extendXIso embedding (i := 0) (i' := 3) (by decide)).hom ≫ z.f0
  | .ofNat (_ + 4) => 0
  | .negSucc _ => 0

theorem component_eq_zero (z : Cocycle P K) (k : ℤ) (h : k < 0 ∨ 3 < k) :
    component z k = 0 := by
  match k with
  | .ofNat (n + 4) => rfl
  | .negSucc n => rfl
  | .ofNat 0 | .ofNat 1 | .ofNat 2 | .ofNat 3 => omega

/-- The signs on the two lowest sheaf degrees implement the Čech total convention. -/
def chainMap (z : Cocycle P K) : P.extend embedding ⟶ K where
  f := component z
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    by_cases hlo : i < -1
    · rw [component_eq_zero z i (Or.inl (by omega)), component_eq_zero z (i + 1) (Or.inl (by omega))]
      simp
    by_cases hhi : 3 < i
    · rw [component_eq_zero z i (Or.inr hhi), component_eq_zero z (i + 1) (Or.inr (by omega))]
      simp
    have ilo : -1 ≤ i := by omega
    have ihi : i ≤ 3 := by omega
    interval_cases i
    · change 0 ≫ K.d (-1) 0 = (P.extend embedding).d (-1) 0 ≫ component z 0
      rw [P.extend_d_eq embedding (i := 4) (j := 3) (i' := -1) (j' := 0) (by decide) (by decide)]
      simp [component, Category.assoc, z.compat4]
    · change component z 0 ≫ K.d 0 1 = (P.extend embedding).d 0 1 ≫ component z 1
      rw [P.extend_d_eq embedding (i := 3) (j := 2) (i' := 0) (j' := 1) (by decide) (by decide)]
      simp [component, Category.assoc, z.compat3]
    · change component z 1 ≫ K.d 1 2 = (P.extend embedding).d 1 2 ≫ component z 2
      rw [P.extend_d_eq embedding (i := 2) (j := 1) (i' := 1) (j' := 2) (by decide) (by decide)]
      simp [component, Category.assoc, z.compat2]
    · change component z 2 ≫ K.d 2 3 = (P.extend embedding).d 2 3 ≫ component z 3
      rw [P.extend_d_eq embedding (i := 1) (j := 0) (i' := 2) (j' := 3) (by decide) (by decide)]
      simp [component, Category.assoc, z.compat1]
    · change component z 3 ≫ K.d 3 4 = (P.extend embedding).d 3 4 ≫ 0
      simp [component, Category.assoc, z.closed]

@[simp] theorem chainMap_vertex (z : Cocycle P K) :
    (P.extendXIso embedding (i := 0) (i' := 3) (by decide)).inv ≫ (chainMap z).f 3 = z.f0 := by
  simp [chainMap, component]

end CycleQ2.TotalThreeChainMap
end
#print axioms CycleQ2.TotalThreeChainMap.chainMap_vertex
