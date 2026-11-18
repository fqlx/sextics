import Proposal.GeometricPoleReductionGradient
import Proposal.GeometricHodgeEuler
import Proposal.SolutionSupport07Part02

/-!
# Radial contraction of a logarithmic pole on the weighted sextic

The Euler field of the five weighted variables differentiates the actual
weighted equation as six times itself on every ambient localization. It
descends to the hypersurface quotient. Its contraction of a logarithmic
pole has the negative contraction of the old residue as its new residue
representative.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2PoleReductionRadial

open MvPolynomial
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2PoleReductionGradient (Poly weightedEquation)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2PoleReductionLocal (prepend contract_prepend)

variable {K : Type} [CommRing K]

def polynomialEuler : Derivation K (Poly K) (Poly K) :=
  ∑ i : Fin 5, (geometricWeight i • (X i : Poly K)) • pderiv i

theorem polynomialEuler_apply (p : Poly K) :
    polynomialEuler p = ∑ i : Fin 5, geometricWeight i • (X i * pderiv i p) := by
  simpa only [polynomialEuler, Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul, nsmul_eq_mul, mul_assoc] using
    congrFun (map_sum Derivation.coeFnAddMonoidHom
      (fun i : Fin 5 => (geometricWeight i • (X i : Poly K)) • pderiv i) Finset.univ) p

@[simp] theorem polynomialEuler_X (i : Fin 5) :
    polynomialEuler (X i : Poly K) = geometricWeight i • X i := by
  classical
  simp [polynomialEuler_apply, pderiv_X, Pi.single_apply, mul_ite, apply_ite]

theorem polynomialEuler_homogeneous (p : Poly K) (n : ℕ)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : polynomialEuler p = n • p := by
  rw [polynomialEuler_apply, hp.sum_weight_X_mul_pderiv]

variable (S : Submonoid (Poly K))
local notation "B" => Localization S
local notation "ι" => algebraMap (Poly K) B

def radial : Derivation K B B := CycleQ2LocalizationDerivation.extend S polynomialEuler

@[simp] theorem radial_map (p : Poly K) :
    radial S (ι p) = ι (polynomialEuler p) :=
  CycleQ2LocalizationDerivation.extend_map S polynomialEuler p

/-- The true localized Euler field equals the explicit coordinate sum on
every element, including rational functions with inverted gradient factors. -/
theorem radial_local_sum : radial S = ∑ i : Fin 5,
    (geometricWeight i • ι (X i)) • CycleQ2PoleReductionGradient.partial S i := by
  symm
  apply CycleQ2LocalizationDerivation.extend_unique S polynomialEuler
  intro p
  have eval := congrFun (map_sum Derivation.coeFnAddMonoidHom
    (fun i : Fin 5 => (geometricWeight i • ι (X i)) •
      CycleQ2PoleReductionGradient.partial S i) Finset.univ) (ι p)
  calc
    _ = ∑ i : Fin 5, (geometricWeight i • ι (X i)) * CycleQ2PoleReductionGradient.partial S i (ι p) := by
      simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply, Derivation.smul_apply,
        smul_eq_mul] using eval
    _ = _ := by
      rw [polynomialEuler_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [CycleQ2PoleReductionGradient.partial_map, map_nsmul, map_mul,
        nsmul_eq_mul, nsmul_eq_mul, mul_assoc]

theorem radial_homogeneous (p : Poly K) (n : ℕ) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    radial S (ι p) = (n : B) * ι p := by
  rw [radial_map, polynomialEuler_apply, hp.sum_weight_X_mul_pderiv, map_nsmul, nsmul_eq_mul]

theorem radial_equation (φ : CoeffRing →+* K) :
    radial S (ι (weightedEquation φ)) = 6 * ι (weightedEquation φ) :=
  radial_homogeneous S _ 6 (CycleQ2HodgeEuler.family_homogeneous φ)

section Quotient

variable {R : Type} [CommRing R] [Algebra K R]
abbrev divisorIdeal (f : R) : Ideal R := Ideal.span {f}
abbrev Divisor (f : R) := R ⧸ divisorIdeal f

theorem preserves_divisor (f h : R) (E : Derivation K R R) (hE : E f = h * f)
    {a : R} (ha : a ∈ divisorIdeal f) : E a ∈ divisorIdeal f := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
  apply Ideal.mem_span_singleton.mpr
  refine ⟨E b + b * h, ?_⟩
  rw [Derivation.leibniz, hE, smul_eq_mul, smul_eq_mul]
  ring

/-- A derivation tangent to the hypersurface acts on its actual quotient ring. -/
def onDivisor (f h : R) (E : Derivation K R R) (hE : E f = h * f) :
    Derivation K (Divisor f) (Divisor f) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective K (divisorIdeal f))
    (d := E) (by
      intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (preserves_divisor f h E hE (Ideal.Quotient.eq_zero_iff_mem.mp hx)))

@[simp] theorem onDivisor_mk (f h : R) (E : Derivation K R R) (hE : E f = h * f) (a : R) :
    onDivisor f h E hE (Ideal.Quotient.mk (divisorIdeal f) a) =
      Ideal.Quotient.mk (divisorIdeal f) (E a) :=
  Derivation.liftOfSurjective_apply _ _ a

local notation "Ω" => KaehlerDifferential K R

/-- After insertion of a tangent vector field, the logarithmic numerator
retains its splitting, with an explicit regular remainder. -/
theorem contract_logarithmic (n : ℕ) (f h : R) (E : Derivation K R R) (hE : E f = h * f)
    (m : ⋀[R]^(n+2) Ω) (b : ⋀[R]^(n+1) Ω) (c : ⋀[R]^(n+2) Ω)
    (hm : m = prepend (n+1) (KaehlerDifferential.D K R f) b + f • c) :
    interior (n+1) E.liftKaehlerDifferential m =
      prepend n (KaehlerDifferential.D K R f) (-interior n E.liftKaehlerDifferential b) +
      f • (h • b + interior (n+1) E.liftKaehlerDifferential c) := by
  rw [hm, map_add, map_smul, contract_prepend, Derivation.liftKaehlerDifferential_comp_D,
    hE, mul_comm h f, ← smul_smul, map_neg, smul_add]
  abel

end Quotient

def weightedDivisorEuler (φ : CoeffRing →+* K) :
    Derivation K (Divisor (ι (weightedEquation φ))) (Divisor (ι (weightedEquation φ))) :=
  onDivisor _ 6 (radial S) (radial_equation S φ)

end CycleQ2PoleReductionRadial
end

#print axioms CycleQ2PoleReductionRadial.radial_equation
#print axioms CycleQ2PoleReductionRadial.weightedDivisorEuler
#print axioms CycleQ2PoleReductionRadial.contract_logarithmic
