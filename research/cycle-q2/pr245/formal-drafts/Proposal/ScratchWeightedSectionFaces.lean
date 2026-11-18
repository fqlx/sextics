import Proposal.ScratchWeightedSectionCochains
import Proposal.GeometricGradientSimplexFrame
import Proposal.GeometricConeTupleSupport

/-! Restriction of every projected cone-simplex component to a native face and
compatibility with the exact chart differential on the proper intersection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace CycleQ2WeightedSectionFaces
open CycleQ2.Cech
open CycleQ2.Cech.Sections (restrict)
open CycleQ2WeightedSectionCochains
open CycleQ2WeightedProjectedSections (sectionEval sectionEval_coord projected_eq restriction_square)
open CycleQ2WeightedNativeOverlapSection (coordAt)
open CycleQ2WeightedGradientSectionUnits (patch_le_coordinate unit_on_commonOpen)
open CycleQ2WeightedResidueAtlas (Index U normalIndex)
open CycleQ2GeometricHodgeThreefold (threefold toBase equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2WeightedConeChartRestrictions (coord cone_hom_ext)
open CycleQ2WeightedRepresentedForms (Expansion projected)
open CycleQ2HodgeEulerContractionRestriction (pull)
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2LogarithmicPullback (Forms)
open CycleQ2GradientSimplex (divisorMap firstBasis firstBasis_apply)
open CycleQ2WeightedNativeCech (frames)
variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)
variable {p : ℕ} (v : Fin (p+2) → Index) (j : Fin (p+2))
abbrev face (v : Fin (p+2) → Index) (j : Fin (p+2)) := v ∘ j.succAbove

def coneFace : simplexDivisor φ (face v j) →ₐ[k] simplexDivisor φ v :=
  divisorMap (equation φ) (CycleQ2ConeSimplexCochain.support_mono (normalIndex ∘ v) j.succAbove)

@[simp] theorem coneFace_coord (a : Fin 5) :
    coneFace φ v j (coord φ _ a) = coord φ _ a := by
  change divisorMap _ _ (CycleQ2GradientSimplex.π _ _ (CycleQ2GradientSimplex.coord _ _ a)) = _
  rw [CycleQ2GradientSimplex.divisorMap_π, CycleQ2GradientSimplex.ambientMap_coord]
  rfl

/-- On every face the tuple's chosen pivot reads its pulled cone form and
the face's own chosen pivot reads the same form after restriction. -/
theorem face_pull (n : ℕ) (ω : Forms k (simplexDivisor φ (face v j)) (n+2))
    (E : Expansion φ (simplexMonoid φ (face v j)) (n+2) ω) :
    pull (restrict (toBase φ) (faceRestriction (U φ) v j).op) (n+1)
      (pull (read φ (face v j) 0) (n+1) (projected φ _ n ω)) =
    pull (read φ v 0) (n+1) (pull (coneFace φ v j) (n+1) (projected φ _ n ω)) := by
  let w := face v j
  let V := intersection (U φ) v
  let W := intersection (U φ) w
  let hs : V ≤ W := leOfHom (faceRestriction (U φ) v j)
  let hv := intersection_le (U φ) v
  let hw := intersection_le (U φ) w
  let hA := (hw 0).trans (patch_le_coordinate φ (w 0))
  let hB := (hv 0).trans (patch_le_coordinate φ (v 0))
  let h' (a) : V ≤ U φ (w a) := hs.trans (hw a)
  let M := simplexMonoid φ w
  let ga := sectionEval φ M (w 0).1 V (hs.trans hA) (open_units φ w V h' _ _)
  let gb := sectionEval φ M (v 0).1 V hB (open_units φ w V h' _ _)
  have eqA : ga = (restrict (toBase φ) (faceRestriction (U φ) v j).op).comp (read φ w 0) := by
    simpa only [AlgHom.comp_id] using
      restriction_square φ M (w 0).1 W hA M V hs (AlgHom.id k _) (fun _ => rfl) _ _
  have eqB : (read φ v 0).comp (coneFace φ v j) = gb := by
    apply cone_hom_ext φ M
    intro a
    simp only [AlgHom.comp_apply, coneFace_coord, readOn_coord, sectionEval_coord, read,gb]
  let z := projected φ M n ω
  calc
    _ = pull ga (n+1) z := by
      rw [eqA]
      exact (CycleQ2LogarithmicPullback.restrict_comp _ _ _ _).symm
    _ = pull gb (n+1) z :=
      (projected_eq φ M (w 0).1 V (hs.trans hA) (v 0).1 hB _ _ n ω E).symm
    _ = _ := by
      rw [← eqB]
      exact CycleQ2LogarithmicPullback.restrict_comp _ _ _ _

/-- The whole Cech coboundary is restriction of the alternating sum in the
common localized cone divisor. -/
theorem delta_pull (n : ℕ)
    (ω : ∀ w : Fin (p+1) → Index, Forms k (simplexDivisor φ w) (n+2))
    (E : ∀ w, Expansion φ (simplexMonoid φ w) (n+2) (ω w)) :
    tupleDelta (U φ) (Native.P (toBase φ)) p (n+1)
      (fun w => pull (read φ w 0) (n+1) (projected φ _ n (ω w))) v =
    pull (read φ v 0) (n+1) (∑ j : Fin (p+2), (-1:ℤ)^j.val •
      pull (coneFace φ v j) (n+1) (projected φ _ n (ω (face v j)))) := by
  rw [tupleDelta,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  exact congrArg (fun ω' => (-1:ℤ)^j.val • ω') (face_pull φ v j n (ω _) (E _))

/-- The exact exterior derivative on Γ(T,Wᵥ) reads the exterior derivative
of the projected cone cochain on its smooth affine cone divisor. -/
theorem read_d {p : ℕ} (v : Fin (p+1) → Index) (q : ℕ)
    (ω : Forms k (simplexDivisor φ v) q) :
    exteriorD ((frames φ).basis p v) q (pull (read φ v 0) q ω) =
      pull (read φ v 0) (q+1) (exteriorD (CycleQ2ConeSimplexCochain.tupleBasis φ (normalIndex ∘ v)) q ω) :=
  CycleQ2LogarithmicChartDerivative.pull_d (read φ v 0)
    (CycleQ2ConeSimplexCochain.tupleBasis φ (normalIndex ∘ v)) _ (CycleQ2GradientSimplex.divisorBasis_apply _ _ _ _)
    ((frames φ).basis p v) ((frames φ).coords p v) ((frames φ).exact_coord p v) q ω

end CycleQ2WeightedSectionFaces
end
#print axioms CycleQ2WeightedSectionFaces.delta_pull
#print axioms CycleQ2WeightedSectionFaces.read_d
