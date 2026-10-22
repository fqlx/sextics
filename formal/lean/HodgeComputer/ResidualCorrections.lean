import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Hom.Basic

/-!
# Exact residual corrections

The operator and source coordinates are fixed throughout a correction chain.
Each step removes only the difference between its incoming and outgoing
remainders. Coordinate changes and normalized traces may translate a step
once their additive maps satisfy the stated operator identity; injectivity
is not required. Concrete residue, density, trace and certificate bridges
remain application obligations.
-/

namespace HodgeComputer.ResidualCorrections

open scoped BigOperators

variable {X Y X' Y' : Type*}
variable [AddCommGroup X] [AddCommGroup Y]
variable [AddCommGroup X'] [AddCommGroup Y']

/-- A correction carries its exact effect on the remaining source. -/
structure Correction (L : X →+ Y) (before after : Y) where
  value : X
  identity : L value = before - after

namespace Correction

/-- A step that leaves its source unchanged. -/
def refl (L : X →+ Y) (r : Y) : Correction L r r where
  value := 0
  identity := by simp

/-- Sequential corrections add; their shared intermediate remainder cancels. -/
def trans {L : X →+ Y} {a b c : Y}
    (h : Correction L a b) (k : Correction L b c) : Correction L a c where
  value := h.value + k.value
  identity := by rw [map_add, h.identity, k.identity, sub_add_sub_cancel]

/-- Transport both the correction and its source through a proved commuting
square. This also allows a noninjective source map, such as normalized trace. -/
def translate {L : X →+ Y} {L' : X' →+ Y'} {a b : Y}
    (T : X →+ X') (U : Y →+ Y')
    (commutes : ∀ x, L' (T x) = U (L x))
    (h : Correction L a b) : Correction L' (U a) (U b) where
  value := T h.value
  identity := by rw [commutes, h.identity, map_sub]

end Correction

/-- Finite corrections telescope with the exact final remainder retained. -/
theorem sum_identity (L : X →+ Y) (R : ℕ → Y) (delta : ℕ → X)
    (n : ℕ) (step : ∀ k < n, L (delta k) = R k - R (k + 1)) :
    L (∑ k ∈ Finset.range n, delta k) = R 0 - R n := by
  revert step
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro step
    rw [Finset.sum_range_succ, map_add,
      ih (fun k hk => step k (Nat.lt_trans hk (Nat.lt_succ_self n))),
      step n (Nat.lt_succ_self n), sub_add_sub_cancel]

/-- A zero final remainder gives the original source exactly. -/
theorem sum_eq_source (L : X →+ Y) (S : Y) (R : ℕ → Y) (delta : ℕ → X)
    (n : ℕ) (initial : R 0 = S) (final : R n = 0)
    (step : ∀ k < n, L (delta k) = R k - R (k + 1)) :
    L (∑ k ∈ Finset.range n, delta k) = S := by
  rw [sum_identity L R delta n step, initial, final, sub_zero]

/-- A chain may provide existence of each correction without a chosen formula. -/
theorem exists_identity (L : X →+ Y) (R : ℕ → Y) (n : ℕ)
    (step : ∀ k < n, ∃ x, L x = R k - R (k + 1)) :
    ∃ x, L x = R 0 - R n := by
  revert step
  induction n with
  | zero => intro _; exact ⟨0, by simp⟩
  | succ n ih =>
    intro step
    obtain ⟨x, hx⟩ := ih (fun k hk => step k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    obtain ⟨y, hy⟩ := step n (Nat.lt_succ_self n)
    exact ⟨x + y, by rw [map_add, hx, hy, sub_add_sub_cancel]⟩

/-- Existential corrections suffice when the last remainder vanishes. -/
theorem exists_eq_source (L : X →+ Y) (S : Y) (R : ℕ → Y) (n : ℕ)
    (initial : R 0 = S) (final : R n = 0)
    (step : ∀ k < n, ∃ x, L x = R k - R (k + 1)) :
    ∃ x, L x = S := by
  obtain ⟨x, hx⟩ := exists_identity L R n step
  exact ⟨x, by simpa only [initial, final, sub_zero] using hx⟩

/-- The whole finite chain translates through the same operator square. -/
theorem translate_sum_identity (L : X →+ Y) (L' : X' →+ Y')
    (T : X →+ X') (U : Y →+ Y')
    (commutes : ∀ x, L' (T x) = U (L x))
    (R : ℕ → Y) (delta : ℕ → X) (n : ℕ)
    (step : ∀ k < n, L (delta k) = R k - R (k + 1)) :
    L' (T (∑ k ∈ Finset.range n, delta k)) = U (R 0) - U (R n) := by
  rw [commutes, sum_identity L R delta n step, map_sub]

end HodgeComputer.ResidualCorrections
