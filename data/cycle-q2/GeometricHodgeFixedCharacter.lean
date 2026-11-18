import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Pi

/-! # The invariant character after contraction by a volume of character two

For a representation identified with the three character components whose
weights are shifted by two, projection to character one inverts the natural
map to the full invariant subspace.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeFixedCharacter

variable (V : ZMod 3 → Type*) [∀ χ, AddCommGroup (V χ)] [∀ χ, Module ℂ (V χ)]
variable {M : Type*} [AddCommGroup M] [Module ℂ M] (E : ((χ : ZMod 3) → V χ) ≃ₗ[ℂ] M)
variable (ρ : Representation ℂ (rootsOfUnity 3 ℂ) M)
variable (hE : ∀ (r : rootsOfUnity 3 ℂ) (a : (χ : ZMod 3) → V χ),
    ρ r (E a) = E (fun χ => ((r.val : ℂ)^2 * (r.val : ℂ)^χ.val) • a χ))

include hE in
private theorem single_fixed (a : V 1) : E (Pi.single (1 : ZMod 3) a) ∈ ρ.invariants := by
  intro r
  rw [hE]
  apply congrArg E
  funext χ
  by_cases h : χ = 1
  · subst χ
    have hr := (mem_rootsOfUnity' 3 r.val).mp r.property
    simp only [ZMod.val_one, pow_one, ← pow_succ, hr, one_smul]
  · simp [Pi.single_eq_of_ne h]

include hE in
private theorem off_character {a : (χ : ZMod 3) → V χ} (ha : E a ∈ ρ.invariants)
    (χ : ZMod 3) (hχ : χ ≠ 1) : a χ = 0 := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))
  have hprim : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  let u := (hprim.isUnit (by decide)).unit
  have hu : (u : ℂ) = ζ := IsUnit.unit_spec _
  let r : rootsOfUnity 3 ℂ := ⟨u,(mem_rootsOfUnity' 3 u).mpr ((congrArg (fun x : ℂ => x^3) hu).trans hprim.pow_eq_one)⟩
  have he := congrFun (E.injective ((hE r a).symm.trans (ha r))) χ
  change ((u : ℂ)^2 * (u : ℂ)^χ.val) • a χ = a χ at he
  rw [hu, ← pow_add] at he
  have hval : χ.val ≠ 1 := by
    intro h
    exact hχ ((ZMod.val_injective 3) (by simpa only [ZMod.val_one] using h))
  have hζ : ζ^(2+χ.val) ≠ 1 := by
    intro h
    have hd := (hprim.pow_eq_one_iff_dvd _).mp h
    have ht := ZMod.val_lt χ
    omega
  have hz : (ζ^(2+χ.val)-1) • a χ = 0 := by rw [sub_smul, one_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hζ)

def equivalence : V 1 ≃ₗ[ℂ] ρ.invariants := by
  classical
  let f := (E.toLinearMap.comp (LinearMap.single ℂ V 1)).codRestrict ρ.invariants
    (single_fixed V E ρ hE)
  refine LinearEquiv.ofBijective f ⟨?_,?_⟩
  · intro a b h
    have h' : E (Pi.single (1 : ZMod 3) a) = E (Pi.single (1 : ZMod 3) b) := congrArg Subtype.val h
    simpa only [Pi.single_eq_same] using congrFun (E.injective h') (1 : ZMod 3)
  · intro v
    let a := E.symm v.val
    have ha : E a ∈ ρ.invariants := (E.apply_symm_apply v.val).symm ▸ v.property
    refine ⟨a 1, Subtype.ext ?_⟩
    change E (Pi.single (1 : ZMod 3) (a 1)) = v.val
    refine (congrArg E (funext fun χ => ?_)).trans (E.apply_symm_apply v.val)
    by_cases h : χ = 1
    · subst χ
      exact Pi.single_eq_same _ _
    · rw [Pi.single_eq_of_ne h, off_character V E ρ hE ha χ h]

end CycleQ2HodgeFixedCharacter
end

#print axioms CycleQ2HodgeFixedCharacter.equivalence
