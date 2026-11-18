import Proposal.ScratchLogarithmicDifferential

/-! Exact chart generators for the ordinary algebraic exterior derivative. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogChartExact
open CycleQ2LogarithmicDifferential CycleQ2LogBasisConnection CycleQ2PoleReductionLocal CycleQ2LogWedge

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable {I : Type} [Fintype I] [LinearOrder I]
variable (b : Module.Basis I R (KaehlerDifferential k R))
local notation "d₁" => KaehlerDifferential.D k R

private def rightWedge (n : ℕ) (ω : Form k R n) : KaehlerDifferential k R →ₗ[R] Form k R (n+1) where
  toFun v := prepend n v ω
  map_add' v w := prepend_add n v w ω
  map_smul' c v := prepend_smul n c v ω

theorem prepend_d (n : ℕ) (f : R) (ω : Form k R n) :
    prepend n (d₁ f) ω = ∑ i, coordDeriv b i f • prepend n (b i) ω := by
  have h := congrArg (rightWedge n ω) (b.sum_repr (d₁ f))
  simpa only [map_sum, map_smul] using h.symm

theorem exteriorD_leibniz_scalar (n : ℕ) (f : R) (ω : Form k R n) :
    exteriorD b n (f • ω) = prepend n (d₁ f) ω + f • exteriorD b n ω := by
  rw [exteriorD_smul, prepend_d b]

/-- Constant scalars commute with exterior differentiation, including the
coefficients of the order-three averaging operator. -/
theorem exteriorD_constant (n : ℕ) (a : k) (ω : Form k R n) :
    exteriorD b n (algebraMap k R a • ω) = algebraMap k R a • exteriorD b n ω := by
  simp only [exteriorD_smul, Derivation.map_algebraMap, zero_smul, Finset.sum_const_zero, zero_add]

/-- The derivative of a pole of any positive order before passing to the
hypersurface. The term of order p+2 is the normal wedge of its numerator. -/
theorem exteriorD_pole (p n : ℕ) (u : Rˣ) (ω : Form k R n) :
    exteriorD b n ((↑u⁻¹ : R)^(p+1) • ω) =
      -((p+1) • ((↑u⁻¹ : R)^(p+2) • prepend n (d₁ (u : R)) ω)) +
      (↑u⁻¹ : R)^(p+1) • exteriorD b n ω := by
  have hu : d₁ (↑u⁻¹ : R) = -(↑u⁻¹ : R)^2 • d₁ (u : R) :=
    (d₁).leibniz_of_mul_eq_one u.inv_mul
  have hp : d₁ ((↑u⁻¹ : R)^(p+1)) = -((p+1) • ((↑u⁻¹ : R)^(p+2) • d₁ (u : R))) := by
    rw [Derivation.leibniz_pow, Nat.add_one_sub_one, hu, neg_smul, smul_neg,
      ← mul_smul, ← pow_add, nsmul_neg]
  rw [exteriorD_leibniz_scalar b, hp]
  change rightWedge n ω _ + _ = _
  simp only [map_neg, map_nsmul, map_smul] <;> rfl

variable (x : I → R) (hx : ∀ i, b i = d₁ (x i))

theorem exteriorD_prepend_exact (n : ℕ) (f : R) (ω : Form k R n) :
    exteriorD b (n+1) (prepend n (d₁ f) ω) =
      -prepend (n+1) (d₁ f) (exteriorD b n ω) := by
  simp only [prepend_d b, map_sum, exteriorD_smul, exteriorD_prepend_basis,
    Finset.sum_add_distrib, smul_neg, Finset.sum_neg_distrib]
  suffices h : (∑ j : I, ∑ i : I, coordDeriv b i (coordDeriv b j f) •
      prepend (n+1) (b i) (prepend n (b j) ω)) = 0 by rw [h, zero_add]
  rw [Finset.sum_comm]
  have hs := sum_prepend_symmetric n b (fun i j => coordDeriv b i (coordDeriv b j f) • ω)
    (fun i j => congrArg (fun c : R => c • ω) (partials_commute b x hx i j f))
  simpa only [map_smul] using hs

private theorem exteriorD_exact (n : ℕ) (f : Fin n → R) :
    exteriorD b n (exteriorPower.ιMulti R n (d₁ ∘ f)) = 0 := by
  induction n with
  | zero =>
    simp only [exteriorD_apply]
    apply Finset.sum_eq_zero
    intro i _
    let v : Fin 0 → I := Fin.elim0
    have h : d₁ ∘ f = b ∘ v := by funext j; exact Fin.elim0 j
    rw [h, coeffD_wedge_basis, map_zero]
  | succ n ih =>
    let g := fun i : Fin n => f i.succ
    have eq : (d₁ ∘ f) = Fin.cons (d₁ (f 0)) (d₁ ∘ g) := by
      funext j
      exact Fin.cases rfl (fun i => rfl) j
    rw [eq, ← prepend_generator, exteriorD_prepend_exact b x hx, ih, map_zero, neg_zero]

/-- The logarithmic product rule is valid for every unit, even if the
chosen frame uses coordinates other than the local defining equation. -/
theorem exteriorD_logarithmic (u : Rˣ) (n : ℕ) (β : Form k R n) (γ : Form k R (n+1)) :
    exteriorD b (n+1) (logarithmic u n β + γ) =
      -logarithmic u (n+1) (exteriorD b n β) + exteriorD b (n+1) γ := by
  have h : d₁ (↑u⁻¹ : R) = -(↑u⁻¹ : R)^2 • d₁ (u : R) :=
    (d₁).leibniz_of_mul_eq_one u.inv_mul
  simp only [map_add, logarithmic, exteriorD_leibniz_scalar b, h, prepend_smul,
    prepend_twice, smul_zero, zero_add, exteriorD_prepend_exact b x hx, smul_neg]

/-- The derivative of a·df₁∧...∧dfₙ is da∧df₁∧...∧dfₙ in every degree. -/
theorem exteriorD_exact_wedge (n : ℕ) (a : R) (f : Fin n → R) :
    exteriorD b n (a • exteriorPower.ιMulti R n (d₁ ∘ f)) =
      exteriorPower.ιMulti R (n+1) (Fin.cons (d₁ a) (d₁ ∘ f)) := by
  rw [exteriorD_leibniz_scalar b, exteriorD_exact b x hx, smul_zero, add_zero, prepend_generator]

end CycleQ2LogChartExact
end
#print axioms CycleQ2LogChartExact.exteriorD_exact_wedge
