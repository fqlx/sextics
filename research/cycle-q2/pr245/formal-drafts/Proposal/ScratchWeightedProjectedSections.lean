import Proposal.ScratchWeightedNativeOverlapSection
import Proposal.ScratchWeightedRepresentedForms
import Proposal.GeometricLogarithmicPullback

/-!
# Actual structure-sheaf sections of projected cone-residue forms

On an open of the proper hypersurface, evaluating the localized divisor of
the cone on a normalized coordinate section induces the pullback on relative
Kähler forms. The resulting projected homogeneous form is independent of the
weight-one pivot. These maps commute with further restriction and with
enlargement of the derivative localization on a face.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace CycleQ2WeightedProjectedSections
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold toBase coordinateOpen)
open CycleQ2WeightedConeChartRestrictions
open CycleQ2WeightedNativeOverlapSection
open CycleQ2WeightedRepresentedForms
open CycleQ2.Cech.Sections (presheaf restrict)
open CycleQ2HodgeEulerContractionRestriction (pull)
open scoped KaehlerDifferential
variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)

abbrev Sections (W : (threefold φ).Opens) := (presheaf (toBase φ)).obj (op W)

variable (M : Submonoid (P k)) (i : Fin 4) (W : (threefold φ).Opens)
  (hi : W ≤ coordinateOpen φ i)
def sectionEval (h : ∀ m : M, IsUnit (MvPolynomial.aeval
    (coordAt φ i W hi : Fin 5 → Sections φ W) (m : P k))) : coneDivisor φ M →ₐ[k] Sections φ W := by
  refine restrictCone φ M (coordAt φ i W hi) h ?_
  have e : (coordAt φ i W hi : Fin 5 → Sections φ W) =
        chartAlg φ i W hi ∘ CycleQ2HodgeEuler.coordinate φ i :=
    funext (fun j => (chartAlg_coordinate φ i W hi j).symm)
  rw [e]; exact normalized_equation φ i _

theorem sectionEval_coord (h : ∀ m : M, IsUnit (MvPolynomial.aeval
    (coordAt φ i W hi : Fin 5 → Sections φ W) (m : P k))) (j : Fin 5) :
    sectionEval φ M i W hi h (coord φ M j) = coordAt φ i W hi j := by
  exact restrictCone_coord φ M _ _ _ j

/-- A coordinate-preserving map of derivative-localized cone divisors commutes
with the genuine structure-sheaf restriction on any further subopen. -/
theorem restriction_square (N : Submonoid (P k)) (V : (threefold φ).Opens) (hVW : V ≤ W)
    (a : coneDivisor φ M →ₐ[k] coneDivisor φ N) (ha : ∀ j, a (coord φ M j) = coord φ N j)
    (h : ∀ m : M, IsUnit (MvPolynomial.aeval (coordAt φ i W hi : Fin 5 → Sections φ W) (m : P k)))
    (h' : ∀ m : N, IsUnit (MvPolynomial.aeval (coordAt φ i V (hVW.trans hi) : Fin 5 → Sections φ V) (m : P k))) :
    (sectionEval φ N i V (hVW.trans hi) h').comp a =
      (restrict (toBase φ) (homOfLE hVW).op).comp (sectionEval φ M i W hi h) := by
  apply cone_hom_ext φ M
  intro j
  simp only [AlgHom.comp_apply, ha, sectionEval_coord]
  rw [← chartAlg_coordinate φ i W hi, ← chartAlg_coordinate φ i V (hVW.trans hi)]
  exact (AlgHom.congr_fun (restrict_comp_chartAlg φ i W hi hVW) _).symm

theorem pull_square (N : Submonoid (P k)) (V : (threefold φ).Opens) (hVW : V ≤ W)
    (a : coneDivisor φ M →ₐ[k] coneDivisor φ N) (ha : ∀ j, a (coord φ M j) = coord φ N j)
    (h : ∀ m : M, IsUnit (MvPolynomial.aeval (coordAt φ i W hi : Fin 5 → Sections φ W) (m : P k)))
    (h' : ∀ m : N, IsUnit (MvPolynomial.aeval (coordAt φ i V (hVW.trans hi) : Fin 5 → Sections φ V) (m : P k)))
    (n : ℕ) (ω : ⋀[coneDivisor φ M]^n Ω[coneDivisor φ M⁄k]) :
    pull (sectionEval φ N i V (hVW.trans hi) h') n (pull a n ω) =
      pull (restrict (toBase φ) (homOfLE hVW).op) n (pull (sectionEval φ M i W hi h) n ω) := by
  refine (CycleQ2LogarithmicPullback.restrict_comp a _ n ω).symm.trans ?_
  rw [restriction_square φ M i W hi N V hVW a ha h h']
  exact CycleQ2LogarithmicPullback.restrict_comp _ _ n ω

theorem projected_eq (j : Fin 4) (hj : W ≤ coordinateOpen φ j)
    (hx : ∀ m : M, IsUnit (MvPolynomial.aeval (coordAt φ i W hi : Fin 5 → Sections φ W) (m : P k)))
    (hy : ∀ m : M, IsUnit (MvPolynomial.aeval (coordAt φ j W hj : Fin 5 → Sections φ W) (m : P k)))
    (n : ℕ) (ω : ⋀[coneDivisor φ M]^(n+2) Ω[coneDivisor φ M⁄k])
    (E : Expansion φ M (n+2) ω) :
    pull (sectionEval φ M j W hj hy) (n+1) (projected φ M n ω) =
      pull (sectionEval φ M i W hi hx) (n+1) (projected φ M n ω) := by
  let g : CycleQ2HodgeEuler.overlap φ i j →ₐ[k] Sections φ W := nativeMap φ i j W hi hj
  have ex : oldPoint φ i j g = coordAt φ i W hi :=
    funext (nativeMap_localCoordinate φ i j W hi hj)
  have ey : newPoint φ i j g = coordAt φ j W hj := by
    funext a
    change g (CycleQ2HodgeEuler.overlapMap φ i j (CycleQ2HodgeEuler.coordinate φ j a)) = _
    rw [CycleQ2HodgeEuler.overlapMap_coordinate]
    exact nativeMap_ratioCoordinate φ i j W hi hj a
  have hx' : ∀ m : M, IsUnit (MvPolynomial.aeval (oldPoint φ i j g) (m : P k)) := ex.symm ▸ hx
  have hy' : ∀ m : M, IsUnit (MvPolynomial.aeval (newPoint φ i j g) (m : P k)) := ey.symm ▸ hy
  have eo : oldCone φ M i j g hx' = sectionEval φ M i W hi hx := by
    apply cone_hom_ext φ M
    intro a
    rw [oldCone, restrictCone_coord, sectionEval_coord, ex]
  have en : newCone φ M i j g hy' = sectionEval φ M j W hj hy := by
    apply cone_hom_ext φ M
    intro a
    rw [newCone, restrictCone_coord, sectionEval_coord, ey]
  rw [← eo, ← en]
  exact projected_glue φ M i j g hx' hy' n ω E

end CycleQ2WeightedProjectedSections
end
#print axioms CycleQ2WeightedProjectedSections.projected_eq
#print axioms CycleQ2WeightedProjectedSections.pull_square
