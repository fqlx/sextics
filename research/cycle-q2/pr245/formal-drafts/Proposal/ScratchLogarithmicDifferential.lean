import Proposal.ScratchLogBasisConnection
import Proposal.ScratchLogWedge
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Lie

/-!
# Exterior differentiation of a logarithmic factor in an exact frame

The powers of the Kähler module have their usual exterior basis. Exterior
differentiation sums the coordinate derivatives of its coefficients,
multiplied on the left by their coordinate differentials. If one coordinate
is the equation of a divisor, the exterior derivative of its logarithmic
differential times a form is minus that logarithmic differential times
the exterior derivative of the form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogarithmicDifferential

open CycleQ2LogBasisConnection CycleQ2PoleReductionLocal CycleQ2LogWedge

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable {I : Type} [Fintype I] [LinearOrder I]
abbrev Form (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (n : ℕ) :=
  ⋀[R]^n (KaehlerDifferential k R)
variable (b : Module.Basis I R (KaehlerDifferential k R))

def coordDeriv (i : I) : Derivation k R R := (b.coord i).compDer (KaehlerDifferential.D k R)

/-- Exterior differential in a frame of exact closed coordinates. -/
def exteriorD (n : ℕ) : Form k R n →+ Form k R (n+1) :=
  ∑ i, (prepend n (b i)).toAddMonoidHom.comp
    (coeffD (b.exteriorPower n) (coordDeriv b i))

theorem exteriorD_apply (n : ℕ) (ω : Form k R n) :
    exteriorD b n ω = ∑ i, prepend n (b i) (coeffD (b.exteriorPower n) (coordDeriv b i) ω) := by
  simp [exteriorD, AddMonoidHom.finset_sum_apply]

private theorem coord_basis_wedge (n : ℕ) (D : Derivation k R R) (i : I)
    (ω : Form k R n) :
    coeffD (b.exteriorPower (n+1)) D (prepend n (b i) ω) =
      prepend n (b i) (coeffD (b.exteriorPower n) D ω) := by
  apply coeffD_natural
  intro s
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, prepend_generator]
  let v : Fin n → I := (Set.powersetCard.ofFinEmbEquiv.symm s)
  have h : Fin.cons (b i) (b ∘ v) = b ∘ Fin.cons i v := by
    funext j
    refine Fin.cases rfl (fun q => ?_) j
    rfl
  rw [show Fin.cons (b i) (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) =
    b ∘ Fin.cons i v from h]
  exact coeffD_wedge_basis b (n+1) D _

theorem exteriorD_prepend_basis (n : ℕ) (i : I) (ω : Form k R n) :
    exteriorD b (n+1) (prepend n (b i) ω) = -prepend (n+1) (b i) (exteriorD b n ω) := by
  simp only [exteriorD_apply, coord_basis_wedge, map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact prepend_swap _ _ _ _

theorem exteriorD_smul (n : ℕ) (r : R) (ω : Form k R n) :
    exteriorD b n (r • ω) =
      (∑ i, (coordDeriv b i r) • prepend n (b i) ω) + r • exteriorD b n ω := by
  simp only [exteriorD_apply, coeffD_smul, map_add, map_smul, Finset.sum_add_distrib,
    Finset.smul_sum]

/-- The coordinate derivations read the unit coordinate matrix on an exact frame. -/
theorem coordDeriv_coordinate (x : I → R) (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (i j : I) : coordDeriv b i (x j) = if j = i then 1 else 0 := by
  change b.repr (KaehlerDifferential.D k R (x j)) i = _
  rw [← hx, Module.Basis.repr_self_apply]

theorem partials_commute (x : I → R) (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (i j : I) (f : R) : coordDeriv b i (coordDeriv b j f) = coordDeriv b j (coordDeriv b i f) := by
  let D := ⁅coordDeriv b i, coordDeriv b j⁆
  have h : D.liftKaehlerDifferential = 0 := by
    apply b.ext
    intro l
    rw [hx, Derivation.liftKaehlerDifferential_comp_D]
    simp only [D, Derivation.commutator_apply, coordDeriv_coordinate b x hx, LinearMap.zero_apply]
    split <;> split <;> simp
  apply sub_eq_zero.mp
  change D f = 0
  rw [← Derivation.liftKaehlerDifferential_comp_D D, h]
  rfl

/-- On a localization in which f is the unit u, dlog f∧β is
u⁻¹ times exterior multiplication by df. -/
def logarithmic (u : Rˣ) (n : ℕ) (β : Form k R n) : Form k R (n+1) :=
  (↑u⁻¹ : R) • prepend n (KaehlerDifferential.D k R (u : R)) β

theorem exteriorD_logarithmic (u : Rˣ) (j : I) (h : KaehlerDifferential.D k R (u : R) = b j)
    (n : ℕ) (β : Form k R n) (γ : Form k R (n+1)) :
    exteriorD b (n+1) (logarithmic u n β + γ) =
      -logarithmic u (n+1) (exteriorD b n β) + exteriorD b (n+1) γ := by
  have h₁ (i : I) : coordDeriv b i (u : R) = if j = i then 1 else 0 := by
    change b.repr (KaehlerDifferential.D k R (u : R)) i = _
    rw [h, Module.Basis.repr_self_apply]
  have hv (i : I) : coordDeriv b i (↑u⁻¹ : R) =
      -(↑u⁻¹ : R)^2 • (if j = i then (1 : R) else 0) := by
    rw [← h₁]
    exact (coordDeriv b i).leibniz_of_mul_eq_one u.inv_mul
  simp only [map_add, logarithmic, h, exteriorD_smul, exteriorD_prepend_basis, smul_neg]
  have hz : (∑ i, coordDeriv b i (↑u⁻¹ : R) •
      (prepend (n+1) (b i) (prepend n (b j) β))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases e : j = i
    · subst i
      simp [prepend_twice]
    · simp [hv, e]
  rw [hz, zero_add]

end CycleQ2LogarithmicDifferential
end
#print axioms CycleQ2LogarithmicDifferential.exteriorD_logarithmic
