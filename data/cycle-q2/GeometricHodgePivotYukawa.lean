import Proposal.GeometricHodgePivotTangentCocycle
import Proposal.GeometricHodgeCoordinateVolume
import Proposal.GeometricHodgeEulerTriplePairing
import Proposal.GeometricHodgeNormalDeformations

/-!
# The moving projective triple normal-connecting fraction

On the fourfold pivot intersection the actual oriented volume evaluates on
the three intrinsic tangent edges to 2w·pqr divided by the four signed
homogeneous partials. Equivalently its numerator over the four degree-six
generators xᵢFᵢ is 2w·pqr·x₀x₁x₂x₃. This identity uses the original
moving sextic and its projective differential sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgePivotYukawa

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeTwistRatios
open CycleQ2HodgeTwistGradientCover (pivotOpen)
open CycleQ2HodgePivotTangentCocycle (h₀ d value tangentEdge radial edge_coordinates)
open CycleQ2HodgeEulerTriplePairing (pairing pairing_eval)
open CycleQ2HodgeEulerTripleContraction (triple_exterior_wedge)
open CycleQ2HodgeEulerTangentSheaf (cotangent tangent)
open CycleQ2HodgeEulerContractionSheaf (evaluateOn)
open CycleQ2GeometricDifferentialChartTransport (chartTop)
open CycleQ2GeometricExteriorSheaf (exteriorSection)
open CycleQ2HodgeCoordinateVolume (forms restrictedOmega partial_volume)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open scoped Matrix

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))
variable (V : (threefold φ).Opens) (h : ∀ i : Fin 4, V ≤ pivotOpen φ i)

abbrev weightTwo := normalized φ 0 (coord φ 4) (coord_mem_grade φ 4) V (h₀ φ V h)

theorem volume : restrictedOmega φ hg V =
    exteriorSection (threefold φ).sheaf (cotangent (toBase φ)).val 3 V
      (d φ V h 1 • exteriorPower.ιMulti _ 3 (forms φ V (h₀ φ V h))) := by
  rw [map_smul, ← partial_volume φ hg V (h₀ φ V h), ← mul_smul,
    CycleQ2HodgePivotNormalLifts.inverse_partial, one_smul]

def evaluation (p q r : grade φ 6) : Γ(threefold φ,V) :=
  (pairing φ hg).eval V (tangentEdge φ hg V h p 0 1) (tangentEdge φ hg V h q 1 2)
    (tangentEdge φ hg V h r 2 3)

private theorem row (p : grade φ 6) (i j : Fin 4) :
    (fun k => evaluateOn (cotangent (toBase φ)) V (tangentEdge φ hg V h p i j) (chartTop V)
      (forms φ V (h₀ φ V h) k)) =
    CycleQ2HodgeFermatYukawaDeterminant.row (radial φ V h) (d φ V h) i j (value φ V h p) := by
  funext k
  exact edge_coordinates φ hg V h p i j k

theorem evaluation_eq (p q r : grade φ 6) :
    evaluation φ hg V h p q r = 2 * (value φ V h p * value φ V h q * value φ V h r) *
      weightTwo φ V h * ∏ i, d φ V h i := by
  rw [evaluation, pairing_eval, volume φ hg V h, triple_exterior_wedge, row, row, row]
  have hrad : radial φ V h 4 = 2 * weightTwo φ V h := by
    change ((2 : ℕ) : Γ(threefold φ,V)) * _ = _
    norm_num
  exact CycleQ2HodgeFermatYukawaDeterminant.residue_evaluation (radial φ V h) (d φ V h)
    (value φ V h p) (value φ V h q) (value φ V h r) (weightTwo φ V h) hrad

abbrev Poly := MvPolynomial (Fin 5) ℂ
abbrev normalDirection (p : Poly) (hp : p.IsWeightedHomogeneous geometricWeight 6) : grade φ 6 :=
  ⟨quotient φ p, quotient_mem_grade φ p hp⟩
abbrev E := CycleQ2HodgeNormalDeformations.evaluate φ 0 V (h₀ φ V h)

def generator (i : Fin 4) : Poly := X i.castSucc * pderiv i.castSucc (equation φ)
def numerator (p q r : Poly) : Poly := 2 * (p*q*r) * X 4 * ∏ i : Fin 4, X i.castSucc

theorem original_fraction (p q r : Poly) (hp : p.IsWeightedHomogeneous geometricWeight 6)
    (hq : q.IsWeightedHomogeneous geometricWeight 6) (hr : r.IsWeightedHomogeneous geometricWeight 6) :
    evaluation φ hg V h (normalDirection φ p hp) (normalDirection φ q hq) (normalDirection φ r hr) *
      E φ V h (∏ i, generator φ i) = E φ V h (numerator p q r) := by
  let x (i : Fin 4) := E φ V h (X i.castSucc)
  let g (i : Fin 4) := E φ V h (pderiv i.castSucc (equation φ))
  have hg' (i : Fin 4) : d φ V h i * g i = 1 := by
    have hi := (equation_homogeneous φ).pderiv (i := i.castSucc)
      (Nat.sub_add_cancel (show geometricWeight i.castSucc ≤ 6 by fin_cases i <;> decide))
    change d φ V h i * E φ V h (pderiv i.castSucc (equation φ)) = 1
    rw [show E φ V h _ = _ from CycleQ2HodgeNormalDeformations.evaluate_homogeneous φ 0 V (h₀ φ V h) _ hi]
    exact CycleQ2HodgePivotNormalLifts.inverse_partial φ i V (h i) 0 (h₀ φ V h)
  have hprod : (∏ i, d φ V h i) * (∏ i, g i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp only [hg', Finset.prod_const_one]
  have hden : E φ V h (∏ i, generator φ i) = (∏ i, x i) * (∏ i, g i) := by
    rw [← Finset.prod_mul_distrib, map_prod]
    exact Finset.prod_congr rfl fun i _ => map_mul _ _ _
  have hw : weightTwo φ V h = E φ V h (X 4) :=
    (CycleQ2HodgeNormalDeformations.evaluate_homogeneous φ 0 V (h₀ φ V h) _ (isWeightedHomogeneous_X ℂ geometricWeight 4)).symm
  have hv (a : Poly) (ha : a.IsWeightedHomogeneous geometricWeight 6) :
      value φ V h (normalDirection φ a ha) = E φ V h a :=
    (CycleQ2HodgeNormalDeformations.evaluate_homogeneous φ 0 V (h₀ φ V h) a ha).symm
  rw [evaluation_eq, hden, hw, hv, hv, hv]
  simp only [numerator, map_mul, map_ofNat, map_prod]
  change 2 * _ * _ * (∏ i, d φ V h i) * ((∏ i, x i) * (∏ i, g i)) = _
  linear_combination (norm := ring) (2 * (E φ V h p * E φ V h q * E φ V h r) * E φ V h (X 4) * ∏ i, x i) * hprod

end CycleQ2HodgePivotYukawa
end
#print axioms CycleQ2HodgePivotYukawa.evaluation_eq
#print axioms CycleQ2HodgePivotYukawa.original_fraction
