import Proposal.GeometricHodgeEulerTangentToQuotient

/-!
# Independence of the normalized tangent lift from the projective pivot

Changing the chart multiplies each coordinate of weight w by t^w.
Differentiating this change adds the same logarithmic derivative of t
times the weighted radial vector. The projective tangent quotient
therefore gives the same section in either chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentAgreement

open CategoryTheory Limits AlgebraicGeometry
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2GeometricHodgeThreefold (threefold coord coord_mem_grade toBase)
open CycleQ2HodgeTwistRatios (U transition normalized_change)
open CycleQ2HodgeThreefoldTwist (chartFrame chartFrame_transition twist)
open CycleQ2HodgeEulerSheaf CycleQ2HodgeEulerQuotientSections
open CycleQ2HodgeEulerQuotientFrames (ambientEquiv ambientEquiv_radial euler)
open CycleQ2HodgeEulerTangentSheaf (tangent)
open CycleQ2HodgeEulerTangentValues (sectionD nativeAlgebra)
open CycleQ2HodgeEulerTangentToQuotient

private theorem logarithmic_rule {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
    (D : Derivation K A A) (t : Aˣ) (x : A) (w : ℕ) :
    D ((t : A)^w*x) - (t : A)^w*D x =
      ((↑t⁻¹ : A)*D (t : A)) * ((w:A) * ((t:A)^w*x)) := by
  cases w with
  | zero => simp
  | succ n =>
    have h : (↑t⁻¹ : A)*(t:A) = 1 := t.inv_mul
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    simp only [nsmul_eq_mul, smul_eq_mul, Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one]
    rw [pow_succ]
    linear_combination -((n+1:A)*x*(t:A)^n*D (t:A)) * h

variable (φ : CoeffRing →+* ℂ) (i k : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (hk : V ≤ U φ k)

private theorem coordinate_derivative_change (s : Γ(tangent (toBase φ),V)) (j : Fin 5) :
    sectionD (toBase φ) s (CycleQ2HodgeTwistRatios.normalized φ i _ (coord_mem_grade φ j) V hi) -
      ((transition φ i k V hi hk : Γ(threefold φ,V)ˣ) : Γ(threefold φ,V))^geometricWeight j *
        sectionD (toBase φ) s (CycleQ2HodgeTwistRatios.normalized φ k _ (coord_mem_grade φ j) V hk) =
      ((↑(transition φ i k V hi hk)⁻¹ : Γ(threefold φ,V)) * sectionD (toBase φ) s (transition φ i k V hi hk : Γ(threefold φ,V))) *
        ((geometricWeight j : Γ(threefold φ,V)) * CycleQ2HodgeTwistRatios.normalized φ i _ (coord_mem_grade φ j) V hi) := by
  let := nativeAlgebra (toBase φ) V
  rw [normalized_change φ i k _ (coord_mem_grade φ j) V hi hk]
  exact logarithmic_rule (sectionD (toBase φ) s) (transition φ i k V hi hk) _ (geometricWeight j)

private theorem raw_change (j : Fin 5) (r : Γ(rawTangent φ,V)) :
    rawCoordinate φ i V hi j r = ((transition φ i k V hi hk : Γ(threefold φ,V)ˣ) : Γ(threefold φ,V)) ^ geometricWeight j *
      rawCoordinate φ k V hk j r := by
  have h := chartFrame_transition φ (geometricWeight j : ℤ) i k V hi hk
    ((Pi.π (pieces φ) j).app V ((kernel.ι (normalMap φ)).app V r))
  simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using h

noncomputable def gauge (s : Γ(tangent (toBase φ),V)) : Γ(twist φ 0,V) :=
  (chartFrame φ 0 i V hi).symm ((↑(transition φ i k V hi hk)⁻¹ : Γ(threefold φ,V)) *
    sectionD (toBase φ) s (transition φ i k V hi hk : Γ(threefold φ,V)))

theorem lifts_differ_by_radial (s : Γ(tangent (toBase φ),V)) :
    lift φ i V hi s - lift φ k V hk s = (radialTangent φ).app V (gauge φ i k V hi hk s) := by
  let := nativeAlgebra (toBase φ) V
  apply (ambientEquiv φ i V hi).injective
  apply Subtype.ext
  rw [ambientEquiv_radial]
  funext j
  change rawCoordinate φ i V hi j (lift φ i V hi s - lift φ k V hk s) =
    chartFrame φ 0 i V hi (gauge φ i k V hi hk s) * euler φ i V hi j
  rw [map_sub, lift_coordinate, raw_change φ i k V hi hk j (lift φ k V hk s), lift_coordinate,
    gauge, LinearEquiv.apply_symm_apply]
  exact coordinate_derivative_change φ i k V hi hk s j

theorem toQuotient_agree (s : Γ(tangent (toBase φ),V)) :
    toQuotient φ i V hi s = toQuotient φ k V hk s := by
  apply sub_eq_zero.mp
  change (cokernel.π (radialTangent φ)).app V (lift φ i V hi s) -
    (cokernel.π (radialTangent φ)).app V (lift φ k V hk s) = 0
  rw [← map_sub, lifts_differ_by_radial φ i k V hi hk s]
  exact congrArg (fun m : twist φ 0 ⟶ tangentQuotient φ => m.app V (gauge φ i k V hi hk s))
    (cokernel.condition (radialTangent φ))

end CycleQ2HodgeEulerTangentAgreement
end

#print axioms CycleQ2HodgeEulerTangentAgreement.toQuotient_agree
