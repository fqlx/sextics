import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Two pole reductions on the derivative cover of a weighted cone

Complementary coordinates for an (n-1)-form record contractions of the volume
by one coordinate vector. An (n-2)-form is recorded by its skew array of double
contractions. The two differentials below use the genuine spatial derivations.
The formulas give a simple-pole Čech cocycle cohomologous to twice the original
meromorphic top form. Only normal derivatives at the vertices of a simplex
are inverted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2WeightedDoublePoleCech
variable {ι k K : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] [Field K] [Algebra k K]
abbrev Flux (ι K : Type*) := ι → K
abbrev Biv (ι K : Type*) := ι → ι → K

def oneIndex (i : ι) (a : K) : Flux ι K := Pi.single i a

def twoIndex (i j : ι) (a : K) : Biv ι K :=
  Pi.single i (Pi.single j a) - Pi.single j (Pi.single i a)

variable (D : ι → Derivation k K K)

def topDerivative : Flux ι K →+ K where
  toFun w := ∑ i, D i (w i)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

def fluxDerivative : Biv ι K →+ Flux ι K where
  toFun w j := ∑ i, D i (w i j)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [Finset.sum_add_distrib]

theorem topDerivative_oneIndex (i : ι) (a : K) :
    topDerivative D (oneIndex i a) = D i a := by
  classical
  change (∑ j, D j ((Pi.single i a : ι → K) j)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem fluxDerivative_single (i j : ι) (a : K) :
    fluxDerivative D (Pi.single i (Pi.single j a)) = oneIndex j (D i a) := by
  classical
  funext l
  change (∑ r, D r ((Pi.single i (Pi.single j a) : ι → ι → K) r l)) = (Pi.single j (D i a) : ι → K) l
  rw [Finset.sum_eq_single i]
  · by_cases hl : l = j
    · subst l; simp
    · simp [Pi.single_eq_of_ne hl]
  · intro r _ hr
    simp [Pi.single_eq_of_ne hr]
  · simp

theorem fluxDerivative_twoIndex (i j : ι) (a : K) :
    fluxDerivative D (twoIndex i j a) = oneIndex j (D i a) - oneIndex i (D j a) := by
  rw [twoIndex, map_sub, fluxDerivative_single, fluxDerivative_single]

private theorem oneIndex_sub (i : ι) (a b : K) :
    oneIndex i (a-b) = oneIndex i a - oneIndex i b := by
  ext l
  by_cases h : l=i
  · subst l; simp [oneIndex]
  · simp [oneIndex, Pi.single_eq_of_ne h]

private theorem oneIndex_add (i : ι) (a b : K) :
    oneIndex i (a+b) = oneIndex i a + oneIndex i b := by
  ext l
  by_cases h : l=i
  · subst l; simp [oneIndex]
  · simp [oneIndex, Pi.single_eq_of_ne h]

variable (F B : K)
abbrev normal (i : ι) := D i F
abbrev coeff (i : ι) := B / normal D F i
abbrev lie (i : ι) := D i (coeff D F B i)
abbrev twiceCoeff (i : ι) := lie D F B i / normal D F i
abbrev pairCoeff (i j : ι) := B / (normal D F i * normal D F j)

/-- Total correction in Čech degree zero. -/
def vertexCorrection (i : ι) : Flux ι K :=
  -oneIndex i (coeff D F B i / F^2) - oneIndex i (twiceCoeff D F B i / F)

/-- Total correction in Čech degree one. -/
def edgeCorrection (i j : ι) : Biv ι K := twoIndex i j (pairCoeff D F B i j / F)

def vertex (i : ι) : K := D i (twiceCoeff D F B i) / F

def edge (i j : ι) : Flux ι K :=
  oneIndex j ((twiceCoeff D F B j + D i (pairCoeff D F B i j))/F) -
  oneIndex i ((twiceCoeff D F B i + D j (pairCoeff D F B i j))/F)

def face (i j l : ι) : Biv ι K :=
  -edgeCorrection D F B j l + edgeCorrection D F B i l - edgeCorrection D F B i j

private theorem div_first (i : ι) (a : K) (hf : F ≠ 0) :
    D i (a/F) = D i a/F - a*normal D F i/F^2 := by
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul,normal]
  field_simp [hf] <;> ring

private theorem div_second (i : ι) (a : K) (hf : F ≠ 0) :
    D i (a/F^2) = D i a/F^2 - 2*a*normal D F i/F^3 := by
  rw [Derivation.leibniz_div, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, normal]
  norm_num only [Nat.reduceSub, pow_one]
  field_simp [hf] <;> ring

/-- The new vertex is the original cubic pole, doubled, minus the true
exterior derivative of the vertex correction. -/
theorem vertex_comparison (i : ι) (hf : F ≠ 0) (hi : normal D F i ≠ 0) :
    vertex D F B i = 2*B/F^3 - topDerivative D (vertexCorrection D F B i) := by
  rw [vertexCorrection,map_sub,map_neg,topDerivative_oneIndex,topDerivative_oneIndex,
    div_second D F i _ hf, div_first D F i _ hf]
  unfold vertex
  change _ = 2*B/F^3 - (-((lie D F B i) / F^2 - 2 * (B / normal D F i) * normal D F i / F^3) -
    (D i (twiceCoeff D F B i) / F - ((lie D F B i) / normal D F i) * normal D F i / F^2))
  field_simp [hf,hi] <;> ring

/-- The two apparent double poles cancel on each double derivative open. -/
theorem edge_comparison (i j : ι) (hf : F ≠ 0) (hi : normal D F i ≠ 0) (hj : normal D F j ≠ 0) :
    edge D F B i j =
      vertexCorrection D F B i - vertexCorrection D F B j +
        fluxDerivative D (edgeCorrection D F B i j) := by
  rw [edgeCorrection,fluxDerivative_twoIndex,div_first D F i _ hf,div_first D F j _ hf]
  have ri : pairCoeff D F B i j * normal D F i / F^2 = coeff D F B j / F^2 := by
    unfold pairCoeff coeff
    field_simp [hf,hi,hj]
  have rj : pairCoeff D F B i j * normal D F j / F^2 = coeff D F B i / F^2 := by
    unfold pairCoeff coeff
    field_simp [hf,hi,hj]
  rw [ri,rj,oneIndex_sub,oneIndex_sub]
  simp only [edge,vertexCorrection,add_div,oneIndex_add]
  abel

/-- The two lower differentials compose to zero on the actual overlap
correction by commutation of the spatial coordinates. -/
theorem correction_closed (comm : ∀ i j a, D i (D j a) = D j (D i a)) (i j : ι) :
    topDerivative D (fluxDerivative D (edgeCorrection D F B i j)) = 0 := by
  rw [edgeCorrection,fluxDerivative_twoIndex,map_sub,topDerivative_oneIndex,topDerivative_oneIndex,
    comm,sub_self]

/-- All double, triple and quadruple-overlap closure equations of the
simple-pole representative. -/
theorem simplePole_cocycle (comm : ∀ i j a, D i (D j a) = D j (D i a))
    (hf : F ≠ 0) (i j l m : ι)
    (hi : normal D F i ≠ 0) (hj : normal D F j ≠ 0) (hl : normal D F l ≠ 0) :
    topDerivative D (edge D F B i j) = vertex D F B j - vertex D F B i ∧
    fluxDerivative D (face D F B i j l) =
      -(edge D F B j l - edge D F B i l + edge D F B i j) ∧
    face D F B j l m - face D F B i l m + face D F B i j m - face D F B i j l = 0 := by
  constructor
  · rw [edge_comparison D F B i j hf hi hj, map_add, map_sub, correction_closed D F B comm,
      vertex_comparison D F B i hf hi, vertex_comparison D F B j hf hj]
    abel
  constructor
  · rw [face, map_sub, map_add, map_neg, edge_comparison D F B i j hf hi hj,
      edge_comparison D F B i l hf hi hl, edge_comparison D F B j l hf hj hl]
    abel
  · unfold face
    abel

end CycleQ2WeightedDoublePoleCech
end
#print axioms CycleQ2WeightedDoublePoleCech.simplePole_cocycle
