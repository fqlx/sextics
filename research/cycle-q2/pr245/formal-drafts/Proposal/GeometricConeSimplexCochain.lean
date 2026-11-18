import Proposal.GeometricConeSimplexNumeratorRestriction
import Proposal.GeometricConeTupleSupport
import Proposal.GeometricLogarithmicResidue

/-! The actual regular logarithmic residues on the cone gradient intersections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexCochain

open MvPolynomial CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2LogarithmicPullback (Forms)
open CycleQ2LogarithmicChartDerivative (pull)
open CycleQ2LogarithmicResidue (localResidue localResidue_restrict)
open CycleQ2ConeSimplexRings
open CycleQ2PoleReductionLocal (prepend split_pole)
open CycleQ2ConeSimplexNumerator (v e f)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k)
local notation "G" => equation φ

/-- A zero derivative selects an empty open. This can happen in a specialized
family, even though all other gradient opens remain meaningful. -/
abbrev Regular (T : Finset (Fin 5)) : Prop := ∀ i ∈ T, pderiv i G ≠ 0

theorem empty_forms {T : Finset (Fin 5)} (hT : ¬Regular φ T) (n : ℕ) :
    Subsingleton (Forms k (Divisor G T) n) := by
  classical
  change ¬∀ i ∈ T, pderiv i G ≠ 0 at hT
  push_neg at hT
  obtain ⟨i,hi,hz⟩ := hT
  letI := divisor_empty G hi hz
  exact Module.subsingleton (Divisor G T) _

/-- Restriction across any inclusion of derivative intersections, with an
arbitrary new normalized partial on the smaller open. -/
theorem pull_res {T U : Finset (Fin 5)} (h : T ⊆ U)
    {i j : Fin 5} (hi : i ∈ T) (hj : j ∈ U) (n : ℕ)
    (m : Forms k (Ambient G T) (n+2))
    (hm : ∃ z, prepend (n+2) (KaehlerDifferential.D k _ (eqn G T)) m = eqn G T • z) :
    pull (restrictDivisor G h) (n+1) (localResidue (quotient G T) (n+1) (normal G hi) m) =
      localResidue (quotient G U) (n+1) (normal G hj) (pull (restrictAmbient G h) (n+2) m) := by
  obtain ⟨z,hz⟩ := hm
  have hD : normal G hj ((restrictAmbient G h) (eqn G T)) = 1 := by
    rw [CycleQ2GradientSimplex.ambientMap_f, normal_eqn]
  exact (localResidue_restrict (quotient G T) (quotient G U) (restrictAmbient G h)
    (restrictDivisor G h) (restriction_square G h) n (eqn G T) (quotient_eqn G T)
    (normal G hi) (normal_eqn G hi) (normal G hj) hD m _ _
    (split_pole (n+1) (normal G hi) (eqn G T) (normal_eqn G hi) m z hz)).symm

/-- Vertex, edge, and face residues. The argument r designates the derivative
used to split off the normal differential on the current common intersection. -/
def rV (T : Finset (Fin 5)) {r i : Fin 5} (hr : r ∈ T) (hi : i ∈ T) :
    Forms k (Divisor G T) 4 := by
  classical
  exact if hT : Regular φ T then localResidue (quotient G T) 4 (normal G hr) (v φ T hT i hi)
    else 0

def rE (T : Finset (Fin 5)) {r i j : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T) :
    Forms k (Divisor G T) 3 := by
  classical
  exact if hT : Regular φ T then localResidue (quotient G T) 3 (normal G hr) (e φ T hT i j hi hj)
    else 0

def rF (T : Finset (Fin 5)) {r i j l : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T)
    (hl : l ∈ T) : Forms k (Divisor G T) 2 := by
  classical
  exact if hT : Regular φ T then localResidue (quotient G T) 2 (normal G hr)
    (f φ T hT i j l hi hj hl) else 0

variable {T : Finset (Fin 5)}
theorem rV_eq (hT : Regular φ T) {r i : Fin 5} (hr : r ∈ T) (hi : i ∈ T) :
    rV φ T hr hi = localResidue (quotient G T) 4 (normal G hr) (v φ T hT i hi) := by
  simp only [rV, dif_pos hT]

theorem rE_eq (hT : Regular φ T) {r i j : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T) :
    rE φ T hr hi hj = localResidue (quotient G T) 3 (normal G hr) (e φ T hT i j hi hj) := by
  simp only [rE, dif_pos hT]

theorem rF_eq (hT : Regular φ T) {r i j l : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T)
    (hl : l ∈ T) :
    rF φ T hr hi hj hl = localResidue (quotient G T) 2 (normal G hr) (f φ T hT i j l hi hj hl) := by
  simp only [rF, dif_pos hT]

def vertex (x : Fin 1 → Fin 5) : Forms k (Divisor G (support x)) 4 :=
  rV φ (support x) (mem_support x 0) (mem_support x 0)

def edge (x : Fin 2 → Fin 5) : Forms k (Divisor G (support x)) 3 :=
  rE φ (support x) (mem_support x 0) (mem_support x 0) (mem_support x 1)

def face (x : Fin 3 → Fin 5) : Forms k (Divisor G (support x)) 2 :=
  rF φ (support x) (mem_support x 0) (mem_support x 0) (mem_support x 1) (mem_support x 2)

end CycleQ2ConeSimplexCochain
end

#print axioms CycleQ2ConeSimplexCochain.pull_res
