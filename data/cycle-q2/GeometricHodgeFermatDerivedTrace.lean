import Proposal.GeometricHodgeDerivedTopTrace
import Proposal.GeometricHodgeTwistTorusChart
import Proposal.GeometricHodgeFermatTorus

/-!
# The Fermat coefficient evaluated by the native third cohomology trace

The standard fourfold overlap is the torus in the zeroth projective frame.
Its section maps to third cohomology by the iterated Mayer–Vietoris
connecting homomorphism. The derived trace of the Fermat fraction reads
the coefficient of the Jacobian socle in the original polynomial product.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatDerivedTrace
open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GenericSexticGradient (seedEvaluation)
open CycleQ2GeometricHodgeThreefold (threefold vertexCoefficient coordinateOpen seed_vertexCoefficient)
open CycleQ2HodgeTwistCech (Vertex)
open CycleQ2HodgeTwistAnchor (torus_le face_frame_evaluation)
open CycleQ2HodgeThreefoldTwist (twist chartFrame)
open CycleQ2HodgeTwistCubicFaces (twistCoordinates)
open CycleQ2GeometricSheafLocalIso (res res_comp res_self)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2HodgeFermatTraceRows (normalForm trace_normalForm Degree power)
open CycleQ2HodgeTwistPolynomial (polynomialMap)
open CycleQ2HodgeFermatTorus (W Ring evaluation z denominator original_monomial)
open CycleQ2HodgeDerivedTopTrace (derivedTrace derivedTrace_connecting topCoordinates)
open CycleQ2HodgeTwistTorusChart (structureLaurentSections)
open CycleQ2HodgeFourOpenStructureHThree (O tripleConnecting)
open CycleQ2GeometricIncidenceProj (geometricWeight)

abbrev ψ := seedEvaluation

theorem good : IsUnit (ψ vertexCoefficient) := by rw [show ψ vertexCoefficient = 1 from seed_vertexCoefficient]; exact isUnit_one

/-- The actual restriction from the common torus to the iterated intersection used by Mayer–Vietoris. -/
def torusSection : Ring →+ CycleQ2HodgeFourOpenStructureHThree.TopSection ψ :=
  res (O ψ) (CycleQ2FourOpenHThree.quad_eq_inf (coordinateOpen ψ)).le

theorem topCoordinates_evaluation (p : CycleQ2HodgeTopCech.TopSection ℂ 0) :
    topCoordinates (structureLaurentSections ψ good) (torusSection (evaluation p)) = p := by
  let E := twistCoordinates ψ 0 good Finset.univ (Finset.mem_univ _) 0
  let F := chartFrame ψ 0 0 W (torus_le ψ 0)
  let h := CycleQ2FourOpenHThree.quad_eq_inf (coordinateOpen ψ)
  have hF : F (E.symm p) = evaluation p := by
    have t := face_frame_evaluation ψ 0 good Finset.univ (Finset.mem_univ _) 0 (E.symm p)
    change F (res (addSheaf (twist ψ 0)) (show W ≤ W from le_rfl) (E.symm p)) =
      evaluation (E (E.symm p)) at t
    simpa only [res_self, AddEquiv.apply_symm_apply] using t
  apply Subtype.ext
  change (E (F.symm (res (O ψ) h.ge (res (O ψ) h.le (evaluation p))))).val = p.val
  rw [res_comp, res_self, ← hF, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

/-- The native cohomology class of a section expressed in the common projective frame. -/
def torusClass := (tripleConnecting ψ good).comp torusSection

/-- The derived trace evaluated directly on this representative. -/
def traceOnTorus : Ring →+ ℂ :=
  (derivedTrace ψ good (structureLaurentSections ψ good)).toAddMonoidHom.comp torusClass

theorem traceOnTorus_evaluation (p : CycleQ2HodgeTopCech.TopSection ℂ 0) :
    traceOnTorus (evaluation p) = CycleQ2HodgeTopCech.trace p := by
  change derivedTrace ψ good _ (tripleConnecting ψ good (torusSection (evaluation p))) = _
  rw [derivedTrace_connecting, topCoordinates_evaluation]

abbrev socleExponent := CycleQ2FermatJacobian.exponent CycleQ2FermatHiggs.socle

theorem trace_monomial (d : Fin 5 →₀ ℕ) (hd : Degree d) (hm : power d ≤ 4) (c : ℂ) :
    traceOnTorus (polynomialMap ψ 0 (monomial d c) * z * denominator) =
      coeff socleExponent (monomial d c) := by
  rw [original_monomial d hd hm c, traceOnTorus_evaluation]
  simpa only [socleExponent, coeff_monomial] using trace_normalForm d hd hm c

/-- Every polynomial of weight eighteen and w-degree at most three satisfies the coefficient formula. -/
theorem trace_polynomial (p : MvPolynomial (Fin 5) ℂ) (hd : p.IsWeightedHomogeneous geometricWeight 18)
    (hm : ∀ d ∈ p.support, d (Fin.last 4) ≤ 3) :
    traceOnTorus (polynomialMap ψ 0 p * z * denominator) = coeff socleExponent p := by
  classical
  let m (d : Fin 5 →₀ ℕ) := monomial d (coeff d p)
  have hsum : ∑ d ∈ p.support, m d = p := p.as_sum.symm
  conv_lhs => rw [← hsum]
  rw [map_sum, Finset.sum_mul, Finset.sum_mul, map_sum]
  conv_rhs => rw [← hsum]
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro d h
  apply trace_monomial d (hd (mem_support_iff.mp h))
  have := hm d h
  unfold power
  omega

/-- Products of the three original degree-six monomials acquire exactly the Fermat socle coefficient. -/
theorem trace_triple (a b c : Fin 5 →₀ ℕ) (α β γ : ℂ)
    (ha : Finsupp.weight geometricWeight a = 6) (hb : Finsupp.weight geometricWeight b = 6)
    (hc : Finsupp.weight geometricWeight c = 6)
    (h'a : a (Fin.last 4) ≤ 1) (h'b : b (Fin.last 4) ≤ 1) (h'c : c (Fin.last 4) ≤ 1) :
    traceOnTorus (polynomialMap ψ 0 (monomial a α * monomial b β * monomial c γ) * z * denominator) =
      coeff socleExponent (monomial a α * monomial b β * monomial c γ) := by
  rw [monomial_mul, monomial_mul]
  apply trace_monomial
  · unfold Degree
    simp only [map_add, ha, hb, hc] <;> decide
  · simp only [power, Finsupp.add_apply]
    omega

end CycleQ2HodgeFermatDerivedTrace
end

#print axioms CycleQ2HodgeFermatDerivedTrace.topCoordinates_evaluation
#print axioms CycleQ2HodgeFermatDerivedTrace.trace_polynomial
#print axioms CycleQ2HodgeFermatDerivedTrace.trace_triple
