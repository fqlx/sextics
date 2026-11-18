import Proposal.GeometricPoleReductionRadial
import Proposal.GeometricLogarithmicResidue

/-!
# Residue of the radial contraction on the hypersurface itself

The sign is obtained before restriction by inserting a tangent vector into
df∧b. Naturality of interior multiplication identifies the remaining
contraction of the regular residue with the true tangent field on the divisor.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2PoleReductionRadial

open CycleQ2LogarithmicPullback (Forms differential differential_D)
open CycleQ2LogarithmicResidue (localResidue localResidue_of_decomposition)
open CycleQ2GeometricExteriorSheaf (exteriorMap)
open CycleQ2PoleReductionLocal (prepend)
open CycleQ2LiteralThreefoldResidueContraction (interior interior_natural)

variable {K R T : Type} [CommRing K] [CommRing R] [CommRing T] [Algebra K R] [Algebra K T]

theorem tangent_compatible (π : R →ₐ[K] T) (E : Derivation K R R) (E' : Derivation K T T)
    (hE : ∀ a, E' (π a) = π (E a)) (ω : KaehlerDifferential K R) :
    E'.liftKaehlerDifferential (differential π ω) = π (E.liftKaehlerDifferential ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D K R)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [differential_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D, hE]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
    simp only [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, map_mul, hx] <;> rfl

/-- Inserting a tangent vector changes the residue by minus the insertion
of its restriction on the divisor. -/
theorem residue_interior (π : R →ₐ[K] T) (n : ℕ) (f h : R) (hf : π f = 0)
    (D E : Derivation K R R) (E' : Derivation K T T) (hD : D f = 1)
    (hE : E f = h * f) (ht : ∀ a, E' (π a) = π (E a))
    (m : Forms K R (n+3)) (b : Forms K R (n+2)) (c : Forms K R (n+3))
    (hm : m = prepend (n+2) (KaehlerDifferential.D K R f) b + f • c) :
    localResidue π (n+1) D (interior (n+2) E.liftKaehlerDifferential m) =
      -interior (n+1) E'.liftKaehlerDifferential (localResidue π (n+2) D m) := by
  rw [localResidue_of_decomposition π n f hf D hD _ _ _
      (contract_logarithmic (n+1) f h E hE m b c hm),
    localResidue_of_decomposition π (n+1) f hf D hD _ _ _ hm, map_neg,
    interior_natural π.toRingHom (differential π) E.liftKaehlerDifferential
      E'.liftKaehlerDifferential (tangent_compatible π E E' ht) (n+1) b]

/-- On the principal quotient the required compatibility follows from the
constructed descended derivation. -/
theorem divisor_residue_interior (n : ℕ) (f h : R)
    (D E : Derivation K R R) (hD : D f = 1) (hE : E f = h * f)
    (m : Forms K R (n+3)) (b : Forms K R (n+2)) (c : Forms K R (n+3))
    (hm : m = prepend (n+2) (KaehlerDifferential.D K R f) b + f • c) :
    let π := Ideal.Quotient.mkₐ K (divisorIdeal f)
    localResidue π (n+1) D (interior (n+2) E.liftKaehlerDifferential m) =
      -interior (n+1) (onDivisor f h E hE).liftKaehlerDifferential
        (localResidue π (n+2) D m) := by
  dsimp only
  apply residue_interior _ n f h _ D E _ hD hE (onDivisor_mk f h E hE) m b c hm
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))

/-- The logarithmic divisibility provided by pole reduction suffices to
obtain the signed residue identity on the actual sextic cone divisor. -/
theorem weighted_residue_interior (S : Submonoid (CycleQ2PoleReductionGradient.Poly K))
    (φ : CycleQ2GenericSexticGradient.CoeffRing →+* K) (i : Fin 5)
    (hi : MvPolynomial.pderiv i (CycleQ2PoleReductionGradient.weightedEquation φ) ∈ S) (n : ℕ)
    (m : Forms K (Localization S) (n+3)) (v : Forms K (Localization S) (n+4))
    (hm : let f := algebraMap (CycleQ2PoleReductionGradient.Poly K) (Localization S)
        (CycleQ2PoleReductionGradient.weightedEquation φ)
      prepend (n+3) (KaehlerDifferential.D K (Localization S) f) m = f • v) :
    let f := algebraMap (CycleQ2PoleReductionGradient.Poly K) (Localization S)
      (CycleQ2PoleReductionGradient.weightedEquation φ)
    let π := Ideal.Quotient.mkₐ K (divisorIdeal f)
    let D := CycleQ2PoleReductionGradient.normal S (CycleQ2PoleReductionGradient.weightedEquation φ) i hi
    localResidue π (n+1) D (interior (n+2) (radial S).liftKaehlerDifferential m) =
      -interior (n+1) (weightedDivisorEuler S φ).liftKaehlerDifferential
        (localResidue π (n+2) D m) := by
  let G := CycleQ2PoleReductionGradient.weightedEquation φ
  let f := algebraMap (CycleQ2PoleReductionGradient.Poly K) (Localization S) G
  let D := CycleQ2PoleReductionGradient.normal S G i hi
  have hD : D f = 1 := CycleQ2PoleReductionGradient.normal_equation S G i hi
  exact divisor_residue_interior n f 6 D (radial S) hD (radial_equation S φ) m _ _
    (CycleQ2PoleReductionLocal.split_pole (n+2) D f hD m v hm)

end CycleQ2PoleReductionRadial
end

#print axioms CycleQ2PoleReductionRadial.residue_interior
#print axioms CycleQ2PoleReductionRadial.divisor_residue_interior

#print axioms CycleQ2PoleReductionRadial.weighted_residue_interior
