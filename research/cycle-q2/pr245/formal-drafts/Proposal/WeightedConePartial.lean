import Mathlib.Algebra.MvPolynomial.PDeriv
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.RingTheory.Derivation.Lie

/-!
# Spatial partial derivatives on the rational function field of the weighted cone

Each coefficient-linear polynomial partial has a unique extension to rational
functions. Their commutator vanishes on the whole function field by the
quotient rule and commutation on polynomial generators.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2WeightedConePartial
open MvPolynomial
variable {ι k : Type*} [Field k] [CharZero k]

abbrev Pol (ι k : Type*) [Field k] := MvPolynomial ι k
abbrev RF (ι k : Type*) [Field k] := FractionRing (Pol ι k)
abbrev value : Pol ι k →+* RF ι k := algebraMap _ _

local instance ratAlgebra : Algebra ℚ (RF ι k) := DivisionRing.toRatAlgebra
local instance ratModule : Module ℚ (RF ι k) := Algebra.toModule

private def rational (i : ι) : Derivation ℚ (RF ι k) (RF ι k) :=
  QuadricContactFraction.extend (F := RF ι k) ((pderiv i : Derivation k (Pol ι k) (Pol ι k)).restrictScalars ℚ)

private theorem rational_map (i : ι) (p : Pol ι k) :
    rational i (value p) = value (pderiv i p) := by
  unfold rational value
  rw [QuadricContactFraction.extend_map] <;> rfl

private theorem rational_constant (i : ι) (a : k) :
    rational i (algebraMap k (RF ι k) a) = 0 := by
  rw [IsScalarTower.algebraMap_apply k (Pol ι k) (RF ι k)]
  change rational i (value (C a)) = 0
  rw [rational_map, pderiv_C, map_zero]

/-- Spatial coordinate derivative over the unchanging coefficient field. -/
def «partial» (i : ι) : Derivation k (RF ι k) (RF ι k) where
  toFun := rational i
  map_add' := (rational i).map_add
  map_smul' c x := by
    simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul, rational_constant, mul_zero, add_zero] <;> simp
  map_one_eq_zero' := (rational i).map_one_eq_zero
  leibniz' := (rational i).leibniz

@[simp] theorem partial_map (i : ι) (p : Pol ι k) :
    «partial» i (value p) = value (pderiv i p) :=
  rational_map i p

theorem ext_fraction {D E : Derivation k (RF ι k) (RF ι k)}
    (h : ∀ p : Pol ι k, D (value p) = E (value p)) : D = E := by
  ext x
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective (Pol ι k) x
  change D (value a / value b) = E (value a / value b)
  rw [Derivation.leibniz_div, Derivation.leibniz_div, h a, h b]

theorem ext_coordinates {D E : Derivation k (RF ι k) (RF ι k)}
    (h : ∀ i : ι, D (value (X i)) = E (value (X i))) : D = E := by
  have hp : D.compAlgebraMap (Pol ι k) = E.compAlgebraMap (Pol ι k) :=
    MvPolynomial.derivation_ext h
  exact ext_fraction (fun p => Derivation.congr_fun hp p)

private theorem partial_partial_X (i j a : ι) :
    «partial» (k := k) i («partial» j (value (X a))) = 0 := by
  rw [partial_map]
  by_cases h : a = j
  · subst a; rw [pderiv_X_self, map_one, Derivation.map_one_eq_zero]
  · rw [pderiv_X_of_ne h, map_zero, map_zero]

theorem partial_commute (i j : ι) (x : RF ι k) :
    «partial» i («partial» j x) = «partial» j («partial» i x) := by
  have eq : ⁅«partial» (k := k) i, «partial» j⁆ = 0 := by
    apply ext_coordinates
    intro a
    rw [Derivation.commutator_apply, partial_partial_X, partial_partial_X, sub_self, Derivation.zero_apply]
  have h := congrArg (fun d : Derivation k (RF ι k) (RF ι k) => d x) eq
  exact sub_eq_zero.mp h

end CycleQ2WeightedConePartial
end

#print axioms CycleQ2WeightedConePartial.partial_map
#print axioms CycleQ2WeightedConePartial.partial_commute
