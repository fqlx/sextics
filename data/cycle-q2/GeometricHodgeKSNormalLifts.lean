import Proposal.GeometricHodgeKSChartPoints
import Proposal.GeometricHodgeEulerQuotientFrames
import Proposal.GeometricHodgeEulerTangentCoordinates

/-!
# Normal-sequence lifts give first-order points of the deformed chart

A lift in the genuine projective normal sequence gives five weighted
velocity sections. Subtracting their radial part normalizes the chosen
weight-one coordinate. The remaining four velocities give a point of
the actual chart equation F − epsilon p over the dual numbers of the
original function ring, on every smaller open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeKSNormalLifts

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeTwistRatios (U) CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2HodgeEulerQuotientFrames (gradients euler euler_zero)
open CycleQ2HodgeEuler (chartMap dehom F normalize reconstruct pairing pairing_apply pairing_insertZero)
open CycleQ2HodgeEulerChartBinding (affineChart)
open CycleQ2HodgeEulerTangentCoordinates (chartSection_partial chartSection_normalized)
open CycleQ2GeometricAffineChartSections (chartSection)
open CycleQ2HodgeKSChartPoints (chartPoint derivative deformationPoint)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricSurfaceFirstOrder (Dual Deformation)

variable {K : Type} [CommRing K] (φ : CoeffRing →+* K) (i : Fin 4)
  (V : (threefold φ).Opens) (hi : V ≤ U φ i)

abbrev eval := chartSection (affineChart φ i) (Over.mk (homOfLE hi))

def rawValues (s : Γ(raw φ,V)) (j : Fin 5) : Γ(threefold φ,V) :=
  chartFrame φ (geometricWeight j) i V hi ((Pi.π (pieces φ) j).app V s)

def velocities (s : Γ(raw φ,V)) : Fin 4 → Γ(threefold φ,V) :=
  normalize i.castSucc (euler φ i V hi) (rawValues φ i V hi s)

theorem derivative_frame (s : Γ(raw φ,V)) :
    derivative (chartPoint φ i (eval φ i V hi)) (velocities φ i V hi s) (F φ i) =
      chartFrame φ 6 i V hi ((normalMap φ).app V s) := by
  let g := gradients φ i V hi
  let r := euler φ i V hi
  let a := rawValues φ i V hi s
  let v := velocities φ i V hi s
  have hj (j : Fin 4) : chartPoint φ i (eval φ i V hi) (pderiv j (F φ i)) = g (i.castSucc.succAbove j) :=
    (congrArg (eval φ i V hi) (CycleQ2HodgeEuler.partial_succAbove φ i j).symm).trans
      (chartSection_partial φ i V hi _)
  have hre := congrArg (pairing g) (reconstruct i.castSucc r (normalized_radial_self φ i V hi) a)
  have hz : pairing g r = 0 := euler_zero φ i V hi
  rw [map_add, map_smul, hz, smul_zero, add_zero, pairing_insertZero] at hre
  calc
    _ = pairing (g ∘ i.castSucc.succAbove) v := by
      rw [pairing_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [hj]; exact mul_comm _ _
    _ = pairing g a := hre
    _ = _ := (pairing_apply g a).trans (normal_frame φ i V hi s).symm

def deformedChartPoint (p : MvPolynomial (Fin 5) K) (hp : p.IsWeightedHomogeneous geometricWeight 6)
    (s : Γ(raw φ,V)) (hs : (normalMap φ).app V s = homogeneousSection φ (quotient φ p) (quotient_mem_grade φ p hp) V) :
    Deformation (F φ i) (dehom i p) →+* Dual Γ(threefold φ,V) :=
  deformationPoint φ i (eval φ i V hi) p (velocities φ i V hi s) (by
    rw [derivative_frame, hs, homogeneousSection_coordinate]
    exact (chartSection_normalized φ i V hi p hp).symm)

theorem deformedChartPoint_coordinates (p : MvPolynomial (Fin 5) K)
    (hp : p.IsWeightedHomogeneous geometricWeight 6) (s : Γ(raw φ,V)) (hs) (j : Fin 4) :
    deformedChartPoint φ i V hi p hp s hs (Ideal.Quotient.mk _ (TrivSqZeroExt.inl (MvPolynomial.X j))) =
      (eval φ i V hi (chartMap φ i (MvPolynomial.X j)), velocities φ i V hi s j) :=
  CycleQ2HodgeKSChartPoints.deformationPoint_coordinates φ i (eval φ i V hi) p _ _ j

end CycleQ2HodgeKSNormalLifts
end

#print axioms CycleQ2HodgeKSNormalLifts.deformedChartPoint_coordinates
