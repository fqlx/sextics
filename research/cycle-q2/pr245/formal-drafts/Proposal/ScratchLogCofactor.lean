import Proposal.ScratchLogarithmicDifferential

/-!
# Differentiating contractions of a coordinate volume

In an exact frame the Cartan identity identifies the anticommutator of
exterior differentiation and contraction by a coordinate vector with the
derivative of the coefficients. The top-degree specializations yield the
signed first and second cofactor formulas for the five-variable cone.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogCofactor
open CycleQ2LogBasisConnection CycleQ2PoleReductionLocal CycleQ2LogarithmicDifferential
open CycleQ2LiteralThreefoldResidueContraction (interior interior_wedge)

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable {I : Type} [Fintype I] [LinearOrder I]
variable (b : Module.Basis I R (KaehlerDifferential k R))

private theorem coeffD_interior_generator (n : ℕ) (D : Derivation k R R) (i : I)
    (v : Fin (n+1) → I) :
    coeffD (b.exteriorPower n) D (interior n (b.coord i) (exteriorPower.ιMulti R (n+1) (b ∘ v))) = 0 := by
  rw [interior_wedge, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hw : coeffD (b.exteriorPower n) D (exteriorPower.ιMulti R n (j.removeNth (b ∘ v))) = 0 := by
    exact coeffD_wedge_basis b n D (j.removeNth v)
  rw [map_zsmul, Module.Basis.coord_apply, Function.comp_apply, Module.Basis.repr_self_apply]
  by_cases e : v j = i <;> simp [e, hw]

/-- A constant coordinate covector commutes with the coefficient derivative. -/
theorem coeffD_interior (n : ℕ) (D : Derivation k R R) (i : I) (ω : Form k R (n+1)) :
    coeffD (b.exteriorPower n) D (interior n (b.coord i) ω) =
      interior n (b.coord i) (coeffD (b.exteriorPower (n+1)) D ω) := by
  apply coeffD_natural
  intro s
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  exact coeffD_interior_generator b n D i _

theorem cartan (n : ℕ) (i : I) (ω : Form k R (n+1)) :
    exteriorD b n (interior n (b.coord i) ω) +
        interior (n+1) (b.coord i) (exteriorD b (n+1) ω) =
      coeffD (b.exteriorPower (n+1)) (coordDeriv b i) ω := by
  classical
  simp only [exteriorD_apply, map_sum, contract_prepend, coeffD_interior, ← Finset.sum_add_distrib]
  have h (j : I) : (b.coord i) (b j) = if j = i then 1 else 0 := b.repr_self_apply j i
  have hc (x y : Form k R (n+1)) : x + (y - x) = y := by abel
  simp_rw [hc, h, ite_smul, one_smul, zero_smul]
  simp

section Cone

variable (B : Module.Basis (Fin 5) R (KaehlerDifferential k R))

def volume : Form k R 5 := exteriorPower.ιMulti R 5 B

private theorem coeffD_volume (D : Derivation k R R) :
    coeffD (B.exteriorPower 5) D (volume B) = 0 :=
  coeffD_wedge_basis B 5 D id

/-- Differentiation of the first signed cofactor in the coordinate volume. -/
theorem first (a : R) (i : Fin 5) :
    exteriorD B 4 (a • interior 4 (B.coord i) (volume B)) =
      coordDeriv B i a • volume B := by
  haveI := six_subsingleton B
  have hd : exteriorD B 5 (a • volume B) = 0 := Subsingleton.elim _ _
  have h := cartan B 4 i (a • volume B)
  simpa only [hd, map_zero, add_zero, map_smul, coeffD_smul, coeffD_volume, smul_zero] using h

/-- Differentiation of two successive coordinate contractions; the left
contraction has positive derivative sign. -/
theorem second (a : R) (i j : Fin 5) :
    exteriorD B 3 (a • interior 3 (B.coord i) (interior 4 (B.coord j) (volume B))) =
      coordDeriv B i a • interior 4 (B.coord j) (volume B) -
        coordDeriv B j a • interior 4 (B.coord i) (volume B) := by
  apply eq_sub_iff_add_eq.mpr
  have h := cartan B 3 i (a • interior 4 (B.coord j) (volume B))
  simpa only [map_smul, first, coeffD_smul, coeffD_interior, coeffD_volume, map_zero,
    smul_zero, add_zero] using h

/-- Differentiation of the threefold contraction occurring on triple
gradient intersections in the cone. -/
theorem third (a : R) (i j l : Fin 5) :
    exteriorD B 2 (a • interior 2 (B.coord i)
      (interior 3 (B.coord j) (interior 4 (B.coord l) (volume B)))) =
      coordDeriv B i a • interior 3 (B.coord j) (interior 4 (B.coord l) (volume B)) -
      coordDeriv B j a • interior 3 (B.coord i) (interior 4 (B.coord l) (volume B)) +
      coordDeriv B l a • interior 3 (B.coord i) (interior 4 (B.coord j) (volume B)) := by
  have h := cartan B 2 i (a • interior 3 (B.coord j) (interior 4 (B.coord l) (volume B)))
  simp only [map_smul, second, map_sub, coeffD_smul, coeffD_interior, coeffD_volume,
    map_zero, smul_zero, add_zero] at h
  rw [← h]
  abel

end Cone
end CycleQ2LogCofactor
end
#print axioms CycleQ2LogCofactor.cartan
#print axioms CycleQ2LogCofactor.first
#print axioms CycleQ2LogCofactor.second
#print axioms CycleQ2LogCofactor.third
