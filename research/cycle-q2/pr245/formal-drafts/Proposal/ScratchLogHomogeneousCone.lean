import Proposal.ScratchLogCofactorWeight
import Proposal.ScratchLogRadialCartan
import Proposal.ScratchLogPolynomialFrame
import Proposal.GeometricSurfaceBindings

/-!
# Contraction of homogeneous meromorphic forms on the sextic cone

The scalar Euler equation makes the Cartan commutator vanish on the
vertex, edge and face forms. The volume has weight six. Its first and
second coordinate contractions have the corresponding coordinate weights
subtracted. The identities hold on any localization, including the ambient
rational function field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogHomogeneousCone

open CycleQ2LogarithmicDifferential CycleQ2LogRadialCartan CycleQ2LogCofactorWeight
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2LogCofactor (volume)
open CycleQ2GeometricIncidenceProj (geometricWeight)

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable {I : Type} [Fintype I] [LinearOrder I]
variable (b : Module.Basis I R (KaehlerDifferential k R))

/-- Vanishing of the Cartan commutator in positive form degree. -/
def Invariant (E : KaehlerDifferential k R →ₗ[R] R) (n : ℕ) (ω : Form k R (n+1)) : Prop :=
  exteriorD b n (interior n E ω) + interior (n+1) E (exteriorD b (n+1) ω) = 0

theorem invariant_sum {J : Type} [Fintype J] (E : KaehlerDifferential k R →ₗ[R] R)
    (n : ℕ) (v : J → Form k R (n+1)) (h : ∀ j, Invariant b E n (v j)) :
    Invariant b E n (∑ j, v j) := by
  unfold Invariant
  simp only [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ => h j

theorem invariant_iff (E : KaehlerDifferential k R →ₗ[R] R) (n : ℕ)
    (ω : Form k R (n+1)) :
    Invariant b E n ω ↔ exteriorD b n (interior n E ω) =
      -interior (n+1) E (exteriorD b (n+1) ω) := by
  exact add_eq_zero_iff_eq_neg

/-- Euler's scalar equation cancels the degree of a constant tensor. -/
theorem homogeneous (x w : I → R) (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (hw : ∀ i, KaehlerDifferential.D k R (w i) = 0) (n : ℕ) {weight : R}
    {ω : Form k R (n+1)} (hω : ConstantWeight b w n weight ω) (a : R)
    (ha : (∑ i, (w i * x i) * coordDeriv b i a) = -weight * a) :
    Invariant b (covector b (fun i => w i * x i)) n (a • ω) := by
  unfold Invariant
  rw [euler b x w hx hw, ← degreeOperator_apply, euler_scalar b w n hω x a, ha]
  simp only [smul_smul, neg_mul, neg_smul, neg_add_cancel]

section Cone

variable (A : Type) [CommRing A] [Algebra k A] [Algebra (MvPolynomial (Fin 5) k) A]
  [IsScalarTower k (MvPolynomial (Fin 5) k) A]
variable (S : Submonoid (MvPolynomial (Fin 5) k)) [IsLocalization S A]

local notation "B" => CycleQ2LogPolynomialFrame.localizedBasis (Fin 5) A S

/-- The coordinates and weights of the original weighted projective cone. -/
def coordinate (i : Fin 5) : A :=
  algebraMap (MvPolynomial (Fin 5) k) A (MvPolynomial.X i)

def w (i : Fin 5) : A := (geometricWeight i : A)

private theorem six : (∑ i, w A i) = 6 := by
  norm_num [w, geometricWeight, Fin.sum_univ_succ]

/-- The true logarithmic Euler covector on the five-variable localization. -/
def radial : KaehlerDifferential k A →ₗ[A] A :=
  covector B fun i => w A i * coordinate (k:=k) A i

/-- The action of the radial derivation on coefficients. -/
def scalarEuler (a : A) : A :=
  ∑ i, (w A i * coordinate (k:=k) A i) * coordDeriv B i a

private theorem invariant_of_weight (n : ℕ) {weight : A} {ω : Form k A (n+1)}
    (hω : ConstantWeight B (w A) n weight ω) (a : A)
    (ha : scalarEuler A S a = -weight*a) : Invariant B (radial A S) n (a • ω) :=
  homogeneous B (coordinate (k:=k) A) (w A)
    (CycleQ2LogPolynomialFrame.localizedBasis_apply (Fin 5) A S)
    (fun i => Derivation.map_natCast _ _) n hω a ha

/-- The degree minus six numerator on each vertex produces an invariant five-form. -/
theorem vertex (a : A) (ha : scalarEuler A S a = (-6 : A)*a) :
    Invariant B (radial A S) 4 (a • volume B) := by
  apply invariant_of_weight A S 4 (constantWeight_volume B (w A))
  simpa only [six] using ha

/-- An edge coefficient has weight equal to its missing coordinate weight minus six. -/
theorem edge (i : Fin 5) (a : A) (ha : scalarEuler A S a = (w A i - 6)*a) :
    Invariant B (radial A S) 3 (a • interior 4 (B.coord i) (volume B)) := by
  apply invariant_of_weight A S 3 (constantWeight_interior B (w A) 3 i
    (constantWeight_volume B (w A)))
  simpa only [six, neg_sub] using ha

/-- A face coefficient has weight equal to the sum of two missing coordinate weights minus six. -/
theorem face (i j : Fin 5) (a : A)
    (ha : scalarEuler A S a = (w A j+w A i-6)*a) :
    Invariant B (radial A S) 2 (a • interior 3 (B.coord i) (interior 4 (B.coord j) (volume B))) := by
  apply invariant_of_weight A S 2 (constantWeight_interior B (w A) 2 i
    (constantWeight_interior B (w A) 3 j (constantWeight_volume B (w A))))
  rw [ha, six]
  ring

theorem horizontal (n : ℕ) (ω : Form k A (n+2)) :
    interior n (radial A S) (interior (n+1) (radial A S) ω) = 0 :=
  CycleQ2LogInteriorAnti.interior_square _ _ _

end Cone
end CycleQ2LogHomogeneousCone
end

#print axioms CycleQ2LogHomogeneousCone.vertex
#print axioms CycleQ2LogHomogeneousCone.edge
#print axioms CycleQ2LogHomogeneousCone.face
#print axioms CycleQ2LogHomogeneousCone.horizontal
