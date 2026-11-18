import Proposal.GeometricHodgeFermatDerivedTrace
import Proposal.GeometricHodgeFermatYukawaRows

/-!
# The native residue determinant and the Fermat socle coefficient

The determinant of the three normal-lift differences carries a factor
two from the radial weight and four inverse factors of six from the
partials. In the native third cohomology trace this gives exactly
the scaled coefficient of the Fermat socle of the original product.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatDeterminantTrace
open AlgebraicGeometry MvPolynomial
open CycleQ2GeometricHodgeThreefold (grade quotient quotient_mem_grade)
open CycleQ2HodgeFermatDerivedTrace (ψ traceOnTorus trace_triple socleExponent)
open CycleQ2HodgeFermatYukawaRows (d w value matrix native_determinant)
open CycleQ2HodgeFermatNormalLifts (invSix six_invSix)
open CycleQ2HodgeFermatTorus (W Ring z denominator denominator_eq x)
open CycleQ2HodgeTwistPolynomial (polynomialMap polynomialMap_normalized)
open CycleQ2HodgeTwistAnchor (torus_le)
open CycleQ2GeometricIncidenceProj (geometricWeight)

def scale : ℂ := 2 * ((6 : ℂ)⁻¹)^4

def numerator (p : MvPolynomial (Fin 5) ℂ) (hp : p.IsWeightedHomogeneous geometricWeight 6) :
    grade ψ 6 := ⟨quotient ψ p, quotient_mem_grade ψ p hp⟩

private def coefficient : ℂ →+* Ring := (polynomialMap ψ 0).comp C

private theorem coefficient_sixth : coefficient ((6 : ℂ)⁻¹) = invSix W := by
  have h : coefficient ((6 : ℂ)⁻¹) * 6 = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg coefficient (inv_mul_cancel₀ (show (6 : ℂ) ≠ 0 by norm_num))
  calc
    _ = coefficient ((6 : ℂ)⁻¹) * (6 * invSix W) := by rw [six_invSix, mul_one]
    _ = (coefficient ((6 : ℂ)⁻¹) * 6) * invSix W := (mul_assoc _ _ _).symm
    _ = _ := by rw [h, one_mul]

private theorem partials : (∏ i, d W (torus_le ψ) i) = (invSix W)^4 * denominator := by
  change (∏ i : Fin 4, invSix W * ((x i)^(-5 : ℤ)).val) = _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, denominator_eq]

theorem native_fraction (p q r : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous geometricWeight 6) (hq : q.IsWeightedHomogeneous geometricWeight 6)
    (hr : r.IsWeightedHomogeneous geometricWeight 6) :
    d W (torus_le ψ) 1 * (matrix W (torus_le ψ) (numerator p hp) (numerator q hq) (numerator r hr)).det =
      polynomialMap ψ 0 (C scale * (p*q*r)) * z * denominator := by
  rw [native_determinant, partials]
  have hv (f : MvPolynomial (Fin 5) ℂ) (hf : f.IsWeightedHomogeneous geometricWeight 6) :
      value W (torus_le ψ) (numerator f hf) = polynomialMap ψ 0 f :=
    (polynomialMap_normalized ψ 0 6 f hf).symm
  have hs : polynomialMap ψ 0 (C scale) = 2 * (invSix W)^4 := by
    change coefficient (2*((6 : ℂ)⁻¹)^4) = _
    rw [map_mul, map_ofNat, map_pow, coefficient_sixth]
  rw [hv, hv, hv, map_mul, hs, map_mul, map_mul]
  change _ * z * _ = _
  ring

/-- The coefficient formula for the residue-normalized determinant of the actual lift differences. -/
theorem trace_native_determinant (a b c : Fin 5 →₀ ℕ) (α β γ : ℂ)
    (ha : Finsupp.weight geometricWeight a = 6) (hb : Finsupp.weight geometricWeight b = 6)
    (hc : Finsupp.weight geometricWeight c = 6)
    (h'a : a (Fin.last 4) ≤ 1) (h'b : b (Fin.last 4) ≤ 1) (h'c : c (Fin.last 4) ≤ 1) :
    traceOnTorus (d W (torus_le ψ) 1 *
      (matrix W (torus_le ψ)
        (numerator (monomial a α) (isWeightedHomogeneous_monomial _ _ _ ha))
        (numerator (monomial b β) (isWeightedHomogeneous_monomial _ _ _ hb))
        (numerator (monomial c γ) (isWeightedHomogeneous_monomial _ _ _ hc))).det) =
      scale * coeff socleExponent (monomial a α * monomial b β * monomial c γ) := by
  have h : C scale * (monomial a α * monomial b β * monomial c γ) =
      monomial a (scale*α) * monomial b β * monomial c γ := by rw [← C_mul_monomial]; ring
  rw [native_fraction, h, trace_triple a b c _ _ _ ha hb hc h'a h'b h'c, ← h, coeff_C_mul]

open CycleQ2FermatHiggs (weightedDegree basisMonomial tangentMonomial basis_properties tangent_properties higgsMatrix)
open CycleQ2FermatJacobian (exponent monomialClass socleTrace_mk socleTrace_triple_eq_higgsMatrix)

private theorem geometricDegree (a : Fin 5 → ℕ) : Finsupp.weight geometricWeight (exponent a) = weightedDegree a :=
  CycleQ2GeometricIncidenceProj.geometricWeight_weight (exponent a)

def upper (i : Fin 33) : grade ψ 6 :=
  numerator (monomial (exponent (basisMonomial i)) 1)
    (isWeightedHomogeneous_monomial _ _ _ ((geometricDegree _).trans (basis_properties i).1))

def tangent (m : Fin 35) : grade ψ 6 :=
  numerator (monomial (exponent (tangentMonomial m)) 1)
    (isWeightedHomogeneous_monomial _ _ _ ((geometricDegree _).trans (tangent_properties m).1))

/-- Matrix of the residue-normalized determinants in the original enumerations of the two
degree-six eigenspaces. The trace uses the original derived cohomology of the Fermat threefold. -/
def traceMatrix (m : Fin 35) : Matrix (Fin 33) (Fin 33) ℂ :=
  Matrix.of fun i j => traceOnTorus
    (d W (torus_le ψ) 1 * (matrix W (torus_le ψ) (upper i) (upper j) (tangent m)).det)

theorem traceMatrix_eq (m : Fin 35) : traceMatrix m = scale • higgsMatrix ℂ m := by
  ext i j
  let a := exponent (basisMonomial i)
  let b := exponent (basisMonomial j)
  let c := exponent (tangentMonomial m)
  have h := trace_native_determinant a b c 1 1 1
    ((geometricDegree _).trans (basis_properties i).1)
    ((geometricDegree _).trans (basis_properties j).1)
    ((geometricDegree _).trans (tangent_properties m).1)
    ((basis_properties i).2.2 (Fin.last 4)) ((basis_properties j).2.2 (Fin.last 4))
    ((tangent_properties m).2.2 (Fin.last 4))
  apply h.trans
  change scale * coeff socleExponent _ = scale * higgsMatrix ℂ m i j
  apply congrArg (scale * ·)
  simpa only [monomialClass, ← map_mul, socleTrace_mk] using socleTrace_triple_eq_higgsMatrix m i j

theorem scale_ne_zero : scale ≠ 0 := by norm_num [scale]

theorem scalar_of_trace_equations (P : Matrix (Fin 33) (Fin 33) ℂ)
    (hp : ∀ m, P.transpose * traceMatrix m = traceMatrix m * P) :
    ∃ c : ℂ, ∀ i j, P i j = if i = j then c else 0 := by
  apply CycleQ2FermatHiggs.scalar_of_higgs_equations P
  intro m
  have he := hp m
  rw [traceMatrix_eq, Matrix.mul_smul, Matrix.smul_mul] at he
  exact smul_right_injective _ scale_ne_zero he

end CycleQ2HodgeFermatDeterminantTrace
end

#print axioms CycleQ2HodgeFermatDeterminantTrace.native_fraction
#print axioms CycleQ2HodgeFermatDeterminantTrace.trace_native_determinant
#print axioms CycleQ2HodgeFermatDeterminantTrace.traceMatrix_eq
#print axioms CycleQ2HodgeFermatDeterminantTrace.scalar_of_trace_equations
