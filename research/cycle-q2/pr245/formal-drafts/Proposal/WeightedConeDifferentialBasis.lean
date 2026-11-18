import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.StdBasis

/-! A list of rational functions of a field extension is a differential basis
when derivations are determined on that list and the coordinate derivations
have identity pairing there. No finite-dimensionality assumption is needed. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeDifferentialBasis
variable {k E ι : Type*} [Field k] [Field E] [Algebra k E] [Fintype ι] [DecidableEq ι]
  (x : ι → E) (D : ι → Derivation k E E)
  (hD : ∀ i j, D i (x j) = if j = i then 1 else 0)
  (hext : ∀ a b : Derivation k E E, (∀ j, a (x j) = b (x j)) → a = b)

abbrev dx (i : ι) := KaehlerDifferential.D k E (x i)

private def components : Ω[E⁄k] →ₗ[E] (ι → E) :=
  LinearMap.pi fun i => (D i).liftKaehlerDifferential

include hD in
private theorem independent : LinearIndependent E (dx (k := k) x) := by
  apply LinearIndependent.of_comp (components D)
  have h : (components D) ∘ dx (k := k) x = Pi.basisFun E ι := by
    funext i j
    change (D j).liftKaehlerDifferential (KaehlerDifferential.D k E (x i)) = Pi.basisFun E ι i j
    simp [hD, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [h]
  exact (Pi.basisFun E ι).linearIndependent

include hext in
private theorem spans : ⊤ ≤ Submodule.span E (Set.range (dx (k := k) x)) := by
  let W := Submodule.span E (Set.range (dx (k := k) x))
  intro z _
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W z).mp
  intro f hf
  have hfzero : f = 0 := by
    apply (KaehlerDifferential.linearMapEquivDerivation k E (M := E)).injective
    apply hext
    intro j
    change f (dx (k := k) x j) = 0
    exact (Submodule.mem_dualAnnihilator f).mp hf _ (Submodule.subset_span ⟨j,rfl⟩)
  rw [hfzero, LinearMap.zero_apply]

def basis : Module.Basis ι E Ω[E⁄k] :=
  Module.Basis.mk (independent x D hD) (spans x hext)

theorem basis_apply (i : ι) : basis x D hD hext i = KaehlerDifferential.D k E (x i) :=
  Module.Basis.mk_apply _ _ i

theorem basis_repr_D (y : E) (i : ι) :
    (basis x D hD hext).repr (KaehlerDifferential.D k E y) i = D i y := by
  have hc : (basis x D hD hext).coord i = (D i).liftKaehlerDifferential := by
    apply (basis x D hD hext).ext
    intro j
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, basis_apply,
      Derivation.liftKaehlerDifferential_comp_D, hD]
  change (basis x D hD hext).coord i (KaehlerDifferential.D k E y) = _
  rw [hc, Derivation.liftKaehlerDifferential_comp_D]

end CycleQ2WeightedConeDifferentialBasis
end

#print axioms CycleQ2WeightedConeDifferentialBasis.basis_repr_D
