import Proposal.GeometricHodgeThreefoldCubicChart

/-!
# The cubic-remainder coefficient for standard torus fractions

For a numerator divided by the (n+1)-st power of all four coordinates,
the degree-two cubic slot contributes its coefficient at (n,n,n) in
the other three variables. Monic polynomial reduction and both
coefficient extractions commute with arbitrary maps of coefficient rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTwistResidueCoefficient
open MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient equation)
open CycleQ2GeometricHodgeThreefoldCubic (Base baseValue baseMonomial expand cubic cubic_monic)
abbrev Poly (R : Type) [CommRing R] := MvPolynomial (Fin 5) R

variable {R S : Type} [CommRing R] [CommRing S] (φ : CoeffRing →+* R)
    (hu : IsUnit (φ vertexCoefficient)) (f : R →+* S)

private theorem map_baseValue (i j : Fin 4) : MvPolynomial.map f (baseValue i j) = baseValue i j := by
  refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp [baseValue]

private theorem map_baseMonomial (i : Fin 4) (e : Fin 5 →₀ ℕ) (c : R) :
    MvPolynomial.map f (baseMonomial i e c) = baseMonomial i e (f c) := by
  simp only [baseMonomial, map_mul, map_prod, map_pow, map_C, map_baseValue]

theorem map_expand (i : Fin 4) (p : Poly R) :
    Polynomial.map (MvPolynomial.map f) (expand i p) = expand i (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [map_monomial, CycleQ2GeometricHodgeThreefoldCubic.expand_monomial,
      CycleQ2GeometricHodgeThreefoldCubic.expand_monomial, Polynomial.map_monomial, map_baseMonomial]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]

private theorem invCoefficient : f (↑hu.unit⁻¹) = ↑(hu.map f).unit⁻¹ := by
  have h : Units.map f.toMonoidHom hu.unit = (hu.map f).unit := Units.ext (by simp)
  exact congrArg Units.val ((map_inv (Units.map f.toMonoidHom) hu.unit).trans (congrArg Inv.inv h))

theorem map_cubic (i : Fin 4) :
    Polynomial.map (MvPolynomial.map f) (cubic φ i hu) = cubic (f.comp φ) i (hu.map f) := by
  simp only [cubic, CycleQ2GeometricHodgeThreefoldCubic.tail, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum, Polynomial.map_monomial,
    map_mul, map_C, map_baseMonomial, invCoefficient, RingHom.comp_apply]

def remainder (p : Poly R) : Polynomial (Base R) := (expand 0 p) %ₘ (cubic φ 0 hu)

def exponent (n : ℕ) : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => n)

def coefficient (n : ℕ) (p : Poly R) : R := MvPolynomial.coeff (exponent n) ((remainder φ hu p).coeff 2)

theorem map_remainder (p : Poly R) : Polynomial.map (MvPolynomial.map f) (remainder φ hu p) =
    remainder (f.comp φ) (hu.map f) (MvPolynomial.map f p) := by
  rw [remainder, Polynomial.map_modByMonic _ (cubic_monic φ 0 hu), map_expand, map_cubic] <;> rfl

theorem map_coefficient (n : ℕ) (p : Poly R) : f (coefficient φ hu n p) =
    coefficient (f.comp φ) (hu.map f) n (MvPolynomial.map f p) := by
  unfold coefficient
  rw [← MvPolynomial.coeff_map, ← Polynomial.coeff_map, map_remainder]

end CycleQ2HodgeTwistResidueCoefficient
end
#print axioms CycleQ2HodgeTwistResidueCoefficient.map_coefficient
