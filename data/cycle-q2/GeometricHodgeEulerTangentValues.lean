import Proposal.GeometricHodgeEulerTangentSheaf
import Proposal.GeometricHodgeEulerOverlap

/-! A section of the intrinsic tangent sheaf differentiates the actual
structure ring on each open. The four normalized coordinates of a vector
field satisfy the moving sextic Jacobian equation on every chart subopen.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option maxHeartbeats 650000
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentValues

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open CycleQ2HodgeEulerTangentSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricAffineChartSections

variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ)) {V : X.Opens}

@[instance_reducible] def nativeAlgebra (V : X.Opens) : Algebra ℂ Γ(X,V) :=
  (coefficientOn X.sheaf (schemeCoefficient f) V).toAlgebra

def sectionD (s : Γ(tangent f,V)) :
    letI := nativeAlgebra f V
    Derivation ℂ Γ(X,V) Γ(X,V) := by
  letI := nativeAlgebra f V
  let D := universalDifferential X.sheaf (schemeCoefficient f)
  refine
    { toFun := fun a => evaluate f s (D.d (X := op V) a)
      map_add' := ?_
      map_smul' := ?_
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · intro a b
    rw [map_add, map_add]
  · intro z a
    let c : Γ(X,V) := coefficientOn X.sheaf (schemeCoefficient f) V z
    have hc : D.d (X := op V) c = 0 := D.d_app z
    change evaluate f s (D.d (c * a)) = c * _
    rw [D.d_mul, hc, smul_zero, add_zero]
    exact (evaluate f s).map_smul c _
  · change evaluate f s (D.d (X := op V) 1) = 0
    exact (congrArg (evaluate f s) (D.d_one (op V))).trans (evaluate f s).map_zero
  · intro a b
    change evaluate f s (D.d (X := op V) (a * b)) = a * evaluate f s (D.d b) + b * evaluate f s (D.d a)
    rw [D.d_mul, map_add]
    exact congrArg₂ (· + ·) ((evaluate f s).map_smul a _) ((evaluate f s).map_smul b _)

theorem sectionD_restrict {W : X.Opens} (h : W ≤ V) (s : Γ(tangent f,V)) (a : Γ(X,V)) :
    sectionD f ((tangent f).val.map (homOfLE h).op s) (X.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE h).op (sectionD f s a) := by
  let D := universalDifferential X.sheaf (schemeCoefficient f)
  change evaluate f _ (D.d (X := op W) _) = _
  exact (congrArg (evaluate f ((tangent f).val.map (homOfLE h).op s)) (D.d_map (homOfLE h).op a)).trans
    (localLinearHomEvaluate_restrict X.sheaf (cotangent f) (functionsModule X) (homOfLE h) s _)

open CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen toBase)
open CycleQ2GenericSexticGradient (CoeffRing)

variable (φ : CoeffRing →+* ℂ) (i : Fin 4) (W : (threefold φ).Opens) (hW : W ≤ coordinateOpen φ i)

abbrev chartFunction (a : chart φ i) : Γ(threefold φ,W) :=
  chartSection (affineChart φ i) (Over.mk (homOfLE hW)) a

def chartEval :
    letI := nativeAlgebra (toBase φ) W
    MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Γ(threefold φ,W) := by
  letI := nativeAlgebra (toBase φ) W
  refine { toRingHom := (chartSection (affineChart φ i) (Over.mk (homOfLE hW))).comp (chartMap φ i).toRingHom,
           commutes' := ?_ }
  intro c
  change chartFunction φ i W hW (chartMap φ i (algebraMap ℂ _ c)) = _
  rw [(chartMap φ i).commutes]
  exact chartSection_complex (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
      (Over.mk (homOfLE hW)) c

/-- The actual tangent evaluation annihilates the dehomogenized hypersurface on every subopen. -/
theorem section_gradient (s : Γ(tangent (toBase φ),W)) :
    ∑ j : Fin 4, chartFunction φ i W hW (chartMap φ i (pderiv j (F φ i))) *
      sectionD (toBase φ) s (chartFunction φ i W hW (chartMap φ i (MvPolynomial.X j))) = 0 := by
  let := nativeAlgebra (toBase φ) W
  have h := CycleQ2PolynomialChainRule.apply (chartEval φ i W hW) (sectionD (toBase φ) s) (F φ i)
  have hF : chartEval φ i W hW (F φ i) = 0 := by
    change chartSection _ _ (chartMap φ i (F φ i)) = 0
    rw [chartMap_F, map_zero]
  rw [hF, map_zero] at h
  exact h.symm

end CycleQ2HodgeEulerTangentValues
end
#print axioms CycleQ2HodgeEulerTangentValues.sectionD_restrict
#print axioms CycleQ2HodgeEulerTangentValues.section_gradient
