import Proposal.ScratchLogEulerCech
import Proposal.ScratchLogCofactorRealization

/-!
# Signed contraction of the actual simplex arrays

The strict upper-triangle realization turns the Euler weights of the
coefficients into Cartan invariance for the full five-, four- and
three-forms. The correcting arrays transport through the same realization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogEulerRealization

open CycleQ2LogarithmicDifferential CycleQ2LogCofactorRealization
open CycleQ2LogHomogeneousCone (Invariant invariant_sum w scalarEuler radial)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2WeightedDoublePoleCech

variable {k : Type} [CommRing k] (K : Type) [Field K] [Algebra k K]
variable [Algebra (MvPolynomial (Fin 5) k) K] [IsScalarTower k (MvPolynomial (Fin 5) k) K]
variable (S : Submonoid (MvPolynomial (Fin 5) k)) [IsLocalization S K]

local notation "B" => CycleQ2LogPolynomialFrame.localizedBasis (Fin 5) K S
local notation "D" => coordDeriv B
local notation "E" => radial K S
local notation "Λ" => scalarEuler K S

theorem invariant_flux (v : Flux (Fin 5) K)
    (hv : ∀ i, Λ (v i) = (w K i-6)*v i) : Invariant B E 3 (flux B v) := by
  rw [flux_apply]
  exact invariant_sum _ _ _ _ fun i => CycleQ2LogHomogeneousCone.edge K S i (v i) (hv i)

theorem invariant_biv (a : Biv (Fin 5) K)
    (ha : ∀ i j, Λ (a i j) = (w K i+w K j-6)*a i j) : Invariant B E 2 (biv B a) := by
  rw [biv_apply]
  apply invariant_sum
  intro i
  apply invariant_sum
  intro j
  split
  · exact CycleQ2LogHomogeneousCone.face K S i j (a i j) (by simpa [add_comm] using ha i j)
  · simp [Invariant]

variable (F N : K)

/-- The four horizontal Čech–de Rham closure equations, written for the
literal twice-reduced components of the supplied equation and numerator. -/
def Cocycle (i j l m : Fin 5) : Prop :=
  let v a := interior 4 E (top B (vertex D F N a))
  let e a c := -interior 3 E (flux B (edge D F N a c))
  let f a c d := interior 2 E (biv B (face D F N a c d))
  exteriorD B 4 (v i) = 0 ∧
  exteriorD B 3 (e i j) = v j-v i ∧
  exteriorD B 2 (f i j l) = -(e j l-e i l+e i j) ∧
  f j l m-f i l m+f i j m-f i j l = 0

/-- The explicit signed meromorphic correction is a Čech–de Rham
coboundary between twice the weighted cubic-pole form and its reduction. -/
def Comparison (i j l : Fin 5) : Prop :=
  let t := interior 4 E (top B (2*N/F^3))
  let v a := interior 4 E (top B (vertex D F N a))
  let e a c := -interior 3 E (flux B (edge D F N a c))
  let f a c d := interior 2 E (biv B (face D F N a c d))
  let u a := -interior 3 E (flux B (vertexCorrection D F N a))
  let q a c := interior 2 E (biv B (edgeCorrection D F N a c))
  v i = t-exteriorD B 3 (u i) ∧
  e i j = u i-u j+exteriorD B 2 (q i j) ∧
  f i j l = -q j l+q i l-q i j

theorem cocycle_of_weights (i j l m : Fin 5) (hF : F ≠ 0)
    (hi : normal D F i ≠ 0) (hj : normal D F j ≠ 0) (hl : normal D F l ≠ 0)
    (hv : Λ (vertex D F N i) = (-6 : K)*vertex D F N i)
    (he : ∀ a, Λ (edge D F N i j a) = (w K a-6)*edge D F N i j a)
    (hf : ∀ a c, Λ (face D F N i j l a c) = (w K a+w K c-6)*face D F N i j l a c) :
    Cocycle K S F N i j l m := by
  obtain ⟨h₁,h₂,h₃⟩ := meromorphic_form_cocycle B
    (CycleQ2LogHomogeneousCone.coordinate (k:=k) K)
    (CycleQ2LogPolynomialFrame.localizedBasis_apply (Fin 5) K S) F N i j l m hF hi hj hl
  exact CycleQ2LogEulerCech.cocycle B E (fun a => top B (vertex D F N a))
    (fun a c => flux B (edge D F N a c)) (fun a c d => biv B (face D F N a c d))
    i j l m (CycleQ2LogHomogeneousCone.vertex K S _ hv)
    (invariant_flux K S _ he) (invariant_biv K S _ hf) h₁ h₂ h₃

theorem comparison_of_weights (i j l : Fin 5) (hF : F ≠ 0)
    (hi : normal D F i ≠ 0) (hj : normal D F j ≠ 0)
    (hu : ∀ a, Λ (vertexCorrection D F N i a) = (w K a-6)*vertexCorrection D F N i a)
    (hq : ∀ a c, Λ (edgeCorrection D F N i j a c) = (w K a+w K c-6)*edgeCorrection D F N i j a c) :
    Comparison K S F N i j l := by
  obtain ⟨h₁,h₂⟩ := meromorphic_form_comparison B F N i j hF hi hj
  exact CycleQ2LogEulerCech.comparison B E (fun a => top B (vertex D F N a))
    (fun a c => flux B (edge D F N a c)) (fun a c d => biv B (face D F N a c d))
    (top B (2*N/F^3)) (fun a => flux B (vertexCorrection D F N a))
    (fun a c => biv B (edgeCorrection D F N a c)) i j l
    (invariant_flux K S _ hu) (invariant_biv K S _ hq) h₁ h₂
    (by simp only [face, map_sub, map_add, map_neg])

end CycleQ2LogEulerRealization
end

#print axioms CycleQ2LogEulerRealization.cocycle_of_weights
#print axioms CycleQ2LogEulerRealization.comparison_of_weights
