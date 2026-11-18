import Proposal.ScratchLogarithmicDifferential

/-!
# Exterior differentiation squares to zero in an exact coordinate frame

The mixed coordinate derivatives on the coefficient ring commute. The
same identity holds on the coefficients of every exterior power. Summing
the resulting symmetric array of second derivatives against successive
exterior multiplications gives zero in every degree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogarithmicDifferential
open CycleQ2LogBasisConnection CycleQ2PoleReductionLocal CycleQ2LogWedge
variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable {I : Type} [Fintype I] [LinearOrder I]
variable (b : Module.Basis I R (KaehlerDifferential k R))

private theorem coefficient_partials_commute (x : I → R)
    (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (n : ℕ) (ω : Form k R n) (i j : I) :
    coeffD (b.exteriorPower n) (coordDeriv b j) (coeffD (b.exteriorPower n) (coordDeriv b i) ω) =
    coeffD (b.exteriorPower n) (coordDeriv b i) (coeffD (b.exteriorPower n) (coordDeriv b j) ω) := by
  apply (b.exteriorPower n).equivFun.injective
  funext s
  simp only [Module.Basis.equivFun_apply, coeffD_coord]
  exact partials_commute b x hx j i _

theorem exteriorD_squared (x : I → R)
    (hx : ∀ i, b i = KaehlerDifferential.D k R (x i)) (n : ℕ) (ω : Form k R n) :
    exteriorD b (n+1) (exteriorD b n ω) = 0 := by
  rw [exteriorD_apply b n ω, map_sum]
  simp_rw [exteriorD_prepend_basis, exteriorD_apply, map_sum]
  rw [Finset.sum_neg_distrib, neg_eq_zero]
  apply sum_prepend_symmetric n (fun i => b i)
  exact coefficient_partials_commute b x hx n ω

end CycleQ2LogarithmicDifferential
end

#print axioms CycleQ2LogarithmicDifferential.exteriorD_squared
