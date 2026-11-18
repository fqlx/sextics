import Proposal.ScratchLogCofactorClosure
import Proposal.GeometricLogarithmicChartDerivative

/-! Čech–de Rham equations for the residues of the normalized cone cofactor forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeLogClosure

open CycleQ2LogarithmicPullback (Forms)
open CycleQ2LogarithmicChartDerivative (pull)
open CycleQ2LogarithmicResidue (localResidue localResidue_zero localResidue_sub localResidue_add localResidue_neg)
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2WeightedConePartial (Pol RF value)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2WeightedConeVertex (grad)
open CycleQ2LogFractionComparison (ambientFrame)
open CycleQ2LogPolynomialFrame (localizedBasis_apply)
open CycleQ2PoleReductionLocal (prepend)
open CycleQ2LogCofactorClosure (vertexMer edgeMer faceMer ambient_closed equation_ne)

variable {k : Type} [Field k] [CharZero k]
local notation "K" => RF (Fin 5) k
local notation "B" => ambientFrame (I := Fin 5) (k := k)

/-- The maps and coordinate frames on a derivative simplex. All numerator
and de Rham identities below are deduced from the explicit rational forms. -/
structure Chart (φ : CoeffRing →+* k) (R S : Type) [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] where
  embed : R →ₐ[k] K
  injective : ∀ n, Function.Injective (pull embed n)
  quotient : R →ₐ[k] S
  equation : R
  equation_field : embed equation = value (CycleQ2GeometricHodgeThreefold.equation φ)
  equation_zero : quotient equation = 0
  normal : Derivation k R R
  normal_equation : normal equation = 1
  ambient : Module.Basis (Fin 5) R (KaehlerDifferential k R)
  x : Fin 5 → R
  ambient_exact : ∀ i, ambient i = KaehlerDifferential.D k R (x i)
  divisor : Module.Basis (Fin 4) S (KaehlerDifferential k S)
  y : Fin 4 → S
  divisor_exact : ∀ i, divisor i = KaehlerDifferential.D k S (y i)

variable {φ : CoeffRing →+* k} {R S : Type} [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] (C : Chart φ R S)

namespace Chart

local notation "F" => value (CycleQ2GeometricHodgeThreefold.equation φ)

abbrev res (n : ℕ) (m : Forms k R (n+1)) : Forms k S n := localResidue C.quotient n C.normal m

/-- The regular numerator of the field form ω with one power of the
equation as denominator. -/
abbrev Realizes (n : ℕ) (m : Forms k R n) (ω : Forms k K n) : Prop :=
  pull C.embed n m = F • ω

abbrev Logarithmic (n : ℕ) (m : Forms k R n) : Prop :=
  ∃ h : Forms k R (n+1), prepend n (KaehlerDifferential.D k R C.equation) m = C.equation • h

theorem realizes_d (hn : F ≠ 0) (n : ℕ)
    (m : Forms k R (n+2)) (dm : Forms k R (n+3))
    (ω : Forms k K (n+2)) (dω : Forms k K (n+3))
    (hm : C.Realizes (n+2) m ω) (hdm : C.Realizes (n+3) dm dω)
    (hd : exteriorD B (n+2) ω = dω) :
    C.Logarithmic (n+2) m ∧ exteriorD C.divisor (n+1) (C.res (n+1) m) = -C.res (n+2) dm := by
  let u : Kˣ := Units.mk0 F hn
  have hu : C.embed C.equation = (u : K) := C.equation_field
  have h0 : (↑u⁻¹ : K) • pull C.embed (n+2) m = ω := by
    rw [hm, smul_smul]; change ((↑u⁻¹ : K) * (u : K)) • ω = ω
    rw [u.inv_mul, one_smul]
  have h1 : (↑u⁻¹ : K) • pull C.embed (n+3) dm = dω := by
    rw [hdm, smul_smul]; change ((↑u⁻¹ : K) * (u : K)) • dω = dω
    rw [u.inv_mul, one_smul]
  have hmer : (↑u⁻¹ : K) • pull C.embed (n+3) dm = exteriorD B (n+2)
      ((↑u⁻¹ : K) • pull C.embed (n+2) m) := by rw [h0,h1,hd]
  have hz := localizedBasis_apply (Fin 5) K (nonZeroDivisors (Pol (Fin 5) k))
  have hlog := CycleQ2LogarithmicChartDerivative.log_condition_of_derivative_of_injective
    C.embed C.injective C.equation u hu C.ambient C.x C.ambient_exact B _ hz (n+2) m dm hmer
  have hres := CycleQ2LogarithmicChartDerivative.residue_d_simple_of_injective C.embed C.injective
    C.quotient C.normal C.equation C.equation_zero C.normal_equation u hu
    C.ambient C.x C.ambient_exact C.divisor C.y C.divisor_exact B _ hz n m dm hmer
  exact ⟨⟨_,hlog⟩, neg_eq_iff_eq_neg.mp hres.symm⟩

theorem vertex (i : Fin 5) (hi : grad i (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0)
    (v : Forms k R 5) (hv : C.Realizes 5 v (vertexMer φ i)) :
    C.Logarithmic 5 v ∧ exteriorD C.divisor 4 (C.res 4 v) = 0 := by
  have h := C.realizes_d (equation_ne φ i hi) 3 v 0 _ 0 hv (by simp [Realizes])
    (ambient_closed φ i i i i hi hi hi).1
  simpa only [res, localResidue_zero, neg_zero] using h

theorem edge (i j : Fin 5) (hi : grad i (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0) (hj : grad j (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0)
    (vi vj : Forms k R 5) (e : Forms k R 4)
    (hvi : C.Realizes 5 vi (vertexMer φ i)) (hvj : C.Realizes 5 vj (vertexMer φ j))
    (he : C.Realizes 4 e (edgeMer φ i j)) :
    C.Logarithmic 4 e ∧ exteriorD C.divisor 3 (C.res 3 e) = C.res 4 vi - C.res 4 vj := by
  have h := C.realizes_d (equation_ne φ i hi) 2 e (vj-vi) (edgeMer φ i j)
    (vertexMer φ j-vertexMer φ i) he
    (by change pull C.embed 5 (vj-vi) = _; rw [map_sub,hvj,hvi,smul_sub])
    (ambient_closed φ i j j j hi hj hj).2.1
  simpa only [res, localResidue_sub, neg_sub] using h

theorem face (i j l : Fin 5) (hi : grad i (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0) (hj : grad j (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0)
    (hl : grad l (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0) (ejl eil eij : Forms k R 4) (a : Forms k R 3)
    (hjl : C.Realizes 4 ejl (edgeMer φ j l)) (hil : C.Realizes 4 eil (edgeMer φ i l))
    (hij : C.Realizes 4 eij (edgeMer φ i j)) (ha : C.Realizes 3 a (faceMer φ i j l)) :
    C.Logarithmic 3 a ∧ exteriorD C.divisor 2 (C.res 2 a) = C.res 3 ejl-C.res 3 eil+C.res 3 eij := by
  have h := C.realizes_d (equation_ne φ i hi) 1 a (-(ejl-eil+eij)) (faceMer φ i j l)
    (-(edgeMer φ j l-edgeMer φ i l+edgeMer φ i j)) ha
    (by change pull C.embed 4 (-(ejl-eil+eij)) = _
        rw [map_neg, map_add, map_sub, hjl, hil, hij, smul_neg, smul_add, smul_sub])
    (ambient_closed φ i j l l hi hj hl).2.2.1
  simpa only [res, localResidue_neg, localResidue_sub, localResidue_add, neg_neg] using h

theorem tetrahedron (i j l m : Fin 5) (hi : grad i (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0)
    (hj : grad j (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0) (hl : grad l (CycleQ2GeometricHodgeThreefold.equation φ) ≠ 0)
    (ajlm ailm aijm aijl : Forms k R 3)
    (hjlm : C.Realizes 3 ajlm (faceMer φ j l m)) (hilm : C.Realizes 3 ailm (faceMer φ i l m))
    (hijm : C.Realizes 3 aijm (faceMer φ i j m)) (hijl : C.Realizes 3 aijl (faceMer φ i j l)) :
    C.res 2 ajlm - C.res 2 ailm + C.res 2 aijm - C.res 2 aijl = 0 := by
  have hd := (ambient_closed φ i j l m hi hj hl).2.2.2
  have h : ajlm-ailm+aijm-aijl = 0 := by
    apply C.injective 3
    simp only [map_sub,map_add,map_zero,hjlm,hilm,hijm,hijl,← smul_sub,← smul_add,hd,smul_zero]
  simpa only [res,localResidue_sub,localResidue_add,localResidue_zero] using congrArg (C.res 2) h

end Chart
end CycleQ2ConeLogClosure
end

#print axioms CycleQ2ConeLogClosure.Chart.vertex
#print axioms CycleQ2ConeLogClosure.Chart.face
#print axioms CycleQ2ConeLogClosure.Chart.tetrahedron
