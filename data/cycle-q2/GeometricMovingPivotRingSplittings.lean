import Proposal.GeometricFamilyDeformation
import Proposal.GeometricSquareZeroAtiyah
import Proposal.GeometricLocalizedDerivations

/-!
# Ring splittings of the ambient test on further principal opens

Every splitting of a square-zero reduction extends after inverting any
lift of the closed denominator. The difference of the extended splittings
is the localization of the original derivation, with the original epsilon
normalization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2MovingPivotRingSplittings

open CycleQ2GeometricKernelLocalization CycleQ2GeometricSquareZeroSplittings
  CycleQ2GeometricLocalizedDerivations

variable {E C : Type} [CommRing E] [CommRing C] [Algebra ℂ E] [Algebra ℂ C]
  [Algebra E C] [IsScalarTower ℂ E C]
variable (e : C ≃ₗ[E] RingHom.ker (algebraMap E C)) (p : E)
variable (σ τ : C →ₐ[ℂ] E) (hσ : ∀ x, algebraMap E C (σ x) = x)
  (hτ : ∀ x, algebraMap E C (τ x) = x)

attribute [local instance] localReductionAlgebra

instance localizedReductionTower : IsScalarTower ℂ (ThickAt E p) (ClosedAt E C p) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    change algebraMap ℂ (ClosedAt E C p) z = localReduction E C p (algebraMap ℂ (ThickAt E p) z)
    rw [IsScalarTower.algebraMap_apply ℂ E (ThickAt E p), localReduction_base,
      ← IsScalarTower.algebraMap_apply ℂ E C, ← IsScalarTower.algebraMap_apply ℂ C (ClosedAt E C p)]

include e hσ in
private theorem split_denominator_unit : IsUnit (algebraMap E (ThickAt E p) (σ (algebraMap E C p))) := by
  let x := σ (algebraMap E C p) - p
  have hx : algebraMap E C x = 0 := by
    rw [show x = σ (algebraMap E C p) - p from rfl, map_sub, hσ, sub_self]
  have hn : IsNilpotent (algebraMap E (ThickAt E p) x) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← map_mul, kernel_mul_zero e x x hx hx, map_zero]
  have h := hn.isUnit_add_left_of_commute (IsLocalization.Away.algebraMap_isUnit p (S := ThickAt E p)) (Commute.all _ _)
  rw [← map_add, show p + x = σ (algebraMap E C p) by dsimp only [x]; abel] at h
  exact h

def localizedSplit : ClosedAt E C p →ₐ[ℂ] ThickAt E p where
  __ := IsLocalization.Away.lift (S := ClosedAt E C p) (g := (algebraMap E (ThickAt E p)).comp σ.toRingHom)
    (algebraMap E C p) (split_denominator_unit e p σ hσ)
  commutes' z := by
    rw [IsScalarTower.algebraMap_apply ℂ C (ClosedAt E C p)]
    change IsLocalization.Away.lift (S := ClosedAt E C p) (g := (algebraMap E (ThickAt E p)).comp σ.toRingHom)
      (algebraMap E C p) (split_denominator_unit e p σ hσ) _ = _
    rw [IsLocalization.Away.lift_eq]
    change algebraMap E (ThickAt E p) (σ (algebraMap ℂ C z)) = _
    rw [σ.commutes, ← IsScalarTower.algebraMap_apply]

theorem localizedSplit_base (x : C) :
    localizedSplit e p σ hσ (algebraMap C (ClosedAt E C p) x) =
      algebraMap E (ThickAt E p) (σ x) :=
  IsLocalization.Away.lift_eq (S := ClosedAt E C p) (g := (algebraMap E (ThickAt E p)).comp σ.toRingHom)
    (algebraMap E C p) (split_denominator_unit e p σ hσ) x

theorem localizedSplit_reduction (x : ClosedAt E C p) :
    algebraMap (ThickAt E p) (ClosedAt E C p) (localizedSplit e p σ hσ x) = x := by
  have h : (localReduction E C p).comp (localizedSplit e p σ hσ).toRingHom = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap E C p))
    apply RingHom.ext
    intro a
    change localReduction E C p (localizedSplit e p σ hσ (algebraMap C (ClosedAt E C p) a)) = _
    rw [localizedSplit_base, localReduction_base, hσ] <;> rfl
  exact RingHom.congr_fun h x

abbrev localizedDifference : Derivation ℂ (ClosedAt E C p) (ClosedAt E C p) :=
  difference (localizedKernelEquiv E C e p) (localizedSplit e p σ hσ) (localizedSplit e p τ hτ)
    (localizedSplit_reduction e p σ hσ) (localizedSplit_reduction e p τ hτ)

theorem localizedDifference_base (x : C) :
    localizedDifference e p σ τ hσ hτ (algebraMap C (ClosedAt E C p) x) =
      algebraMap C (ClosedAt E C p) (difference e σ τ hσ hτ x) := by
  apply epsilon_injective (localizedKernelEquiv E C e p)
  rw [epsilon_difference]
  change _ = (localizedKernelEquiv E C e p (algebraMap C (ClosedAt E C p) (difference e σ τ hσ hτ x))).val
  rw [localizedKernelEquiv_base, localizedSplit_base, localizedSplit_base]
  change _ = algebraMap E (ThickAt E p) (epsilon e (difference e σ τ hσ hτ x))
  rw [epsilon_difference, map_sub]

theorem derivation_ext_localization {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra A B] (S : Submonoid A) [IsLocalization S B] (f g : Derivation ℂ B B)
    (h : ∀ x : A, f (algebraMap A B x) = g (algebraMap A B x)) : f = g := by
  apply Derivation.ext
  intro x
  obtain ⟨⟨a,d⟩, hx⟩ := IsLocalization.surj S x
  have hf := congrArg f hx
  have hg := congrArg g hx
  simp only [Derivation.leibniz, smul_eq_mul, h] at hf hg
  exact (IsLocalization.map_units B d).mul_left_cancel (add_left_cancel (hf.trans hg.symm))

theorem localizedDifference_eq :
    localizedDifference e p σ τ hσ hτ = localizedDerivation (Submonoid.powers (algebraMap E C p))
      (ClosedAt E C p) (difference e σ τ hσ hτ) := by
  apply derivation_ext_localization (A := C) (Submonoid.powers (algebraMap E C p))
  intro x
  rw [localizedDifference_base, localizedDerivation_algebraMap]

/-- The lifted multiplicative defect on the further principal open, up to
the three actual edge corrections. -/
theorem localizedUnitDefect (u v w : (ThickAt E p)ˣ)
    (h : reducedUnit (C := ClosedAt E C p) u * reducedUnit v = reducedUnit w) :
    unitDefect (localizedKernelEquiv E C e p) u v w h =
      (unitCorrection (localizedKernelEquiv E C e p) (localizedSplit e p τ hτ) (localizedSplit_reduction e p τ hτ) v -
       unitCorrection (localizedKernelEquiv E C e p) (localizedSplit e p σ hσ) (localizedSplit_reduction e p σ hσ) w +
       unitCorrection (localizedKernelEquiv E C e p) (localizedSplit e p σ hσ) (localizedSplit_reduction e p σ hσ) u) +
      (localizedDerivation (Submonoid.powers (algebraMap E C p)) (ClosedAt E C p)
        (difference e σ τ hσ hτ)).liftKaehlerDifferential (logDifferential (K := ℂ) (reducedUnit v)) := by
  rw [← localizedDifference_eq e p σ τ hσ hτ]
  exact unitDefect_eq_boundary_add_contraction _ _ _ _ _ u v w h

include hσ in
theorem reduced_splitUnit (g : Cˣ) :
    reducedUnit (C := C) (Units.map σ.toMonoidHom g) = g := by
  apply Units.ext
  exact hσ (g : C)

theorem unitCorrection_splitUnit (g : Cˣ) :
    unitCorrection e σ hσ (Units.map σ.toMonoidHom g) = 0 := by
  apply epsilon_injective e
  rw [epsilon_unitCorrection, map_zero, normalizedUnitValue, reduced_splitUnit σ hσ]
  change σ (g : C) * σ (↑(g⁻¹) : C) - 1 = 0
  rw [← map_mul, g.mul_inv, map_one, sub_self]

/-- The edge correction respects a genuine restriction of split
square-zero rings preserving reduction, epsilon and the chosen splitting. -/
theorem unitCorrection_natural {E' C' : Type} [CommRing E'] [CommRing C']
    [Algebra ℂ E'] [Algebra ℂ C'] [Algebra E' C'] [IsScalarTower ℂ E' C']
    (e' : C' ≃ₗ[E'] RingHom.ker (algebraMap E' C'))
    (σ' : C' →ₐ[ℂ] E') (hσ' : ∀ x, algebraMap E' C' (σ' x) = x)
    (m : E →+* E') (n : C →+* C')
    (hρ : ∀ x, n (algebraMap E C x) = algebraMap E' C' (m x))
    (hε : ∀ x, m (epsilon e x) = epsilon e' (n x))
    (hl : ∀ x, m (σ x) = σ' (n x)) (g : Eˣ) :
    n (unitCorrection e σ hσ g) = unitCorrection e' σ' hσ' (Units.map m.toMonoidHom g) := by
  have hu : Units.map n.toMonoidHom (reducedUnit (C := C) g) =
      reducedUnit (C := C') (Units.map m.toMonoidHom g) := by
    apply Units.ext
    exact hρ (g : E)
  apply epsilon_injective e'
  rw [← hε, epsilon_unitCorrection, epsilon_unitCorrection, map_sub, map_one]
  apply congrArg (· - 1)
  unfold normalizedUnitValue
  rw [map_mul, hl, ← hu, ← map_inv]
  rfl

end CycleQ2MovingPivotRingSplittings
end

#print axioms CycleQ2MovingPivotRingSplittings.localizedSplit
#print axioms CycleQ2MovingPivotRingSplittings.localizedDifference_eq
#print axioms CycleQ2MovingPivotRingSplittings.localizedUnitDefect
