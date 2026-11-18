import Proposal.WeightedConeVertex

/-! The coefficient on a derivative patch of the hypersurface itself is the
quotient of its regular ambient representative. Evaluation at any point of
the hypersurface commutes with this restriction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeVertex

variable {ι k L : Type} [Field k] [CharZero k] [Field L] [CharZero L]
variable (i : ι) (F B : Poly ι k)

abbrev DivisorIdeal : Ideal (GradientRing i F) :=
  Ideal.span {algebraMap (Poly ι k) (GradientRing i F) F}

abbrev DivisorRing := GradientRing i F ⧸ DivisorIdeal i F

def divisorResidue : DivisorRing i F :=
  Ideal.Quotient.mk (DivisorIdeal i F) (residueSection i F B)

variable (v : Poly ι k →+* L) (hg : v (grad i F) ≠ 0) (hf : v F = 0)

def onDivisor : DivisorRing i F →+* L :=
  Ideal.Quotient.lift _ (evalSection i F v hg) (fun a ha =>
    (Ideal.span_singleton_le_iff_mem (RingHom.ker (evalSection i F v hg))).mpr
      (show evalSection i F v hg (algebraMap _ _ F) = 0 from
        (IsLocalization.Away.lift_eq (grad i F) (isUnit_iff_ne_zero.mpr hg) F).trans hf) ha)

theorem onDivisor_residue :
    onDivisor i F v hg hf (divisorResidue i F B) =
      SplitHigherResidue.normalSourceTwo (v B) (v (MvPolynomial.pderiv i B))
        (v (MvPolynomial.pderiv i (MvPolynomial.pderiv i B)))
        (v (grad i F)) (v (MvPolynomial.pderiv i (grad i F)))
        (v (MvPolynomial.pderiv i (MvPolynomial.pderiv i (grad i F)))) / v (grad i F) :=
  evalSection_residue i F B v hg

open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeEuler (dehom)

theorem chart_divisor_density (φ : CoeffRing →+* k) (v₀ : Poly (Fin 4) k →+* L)
    (hn : (v₀.comp (dehom 0).toRingHom) (grad 1 (equation φ)) ≠ 0)
    (hzero : v₀ (CycleQ2HodgeEuler.F φ 0) = 0) :
    onDivisor 1 (equation φ) (v₀.comp (dehom 0).toRingHom) hn hzero
      (divisorResidue 1 (equation φ) (coneNumerator k)) =
        CycleQ2MonicWeightedPrimitiveIdentity.density v₀ (CycleQ2HodgeEuler.F φ 0) :=
  chart_density φ v₀ hn

end CycleQ2WeightedConeVertex
end
#print axioms CycleQ2WeightedConeVertex.chart_divisor_density
