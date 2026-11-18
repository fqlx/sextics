import Proposal.ScratchWeightedProjectedSections
import Proposal.ScratchWeightedGradientSectionUnits
import Proposal.ScratchWeightedNativeCech

/-!
# Projected cone cochains on the actual opens of the proper threefold

The localization at the selected partial derivatives is evaluated in each
structure-sheaf ring on the ordered simplex, by its coordinate sections.
Any of the pivots admitted by the simplex gives the same projected form.
On a vertex, evaluating the assembled Čech cochain gives its restriction to
the actual gradient open, even for the categorical singleton intersection.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace CycleQ2WeightedSectionCochains
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold equation toBase)
open CycleQ2WeightedResidueAtlas (Index U normalIndex)
open CycleQ2WeightedGradientSectionUnits (patch_le_coordinate unit_on_commonOpen)
open CycleQ2WeightedConeChartRestrictions (coneDivisor coord)
open CycleQ2WeightedProjectedSections (Sections sectionEval sectionEval_coord projected_eq pull_square restriction_square)
open CycleQ2WeightedRepresentedForms (Expansion projected)
open CycleQ2WeightedCechPresentations (denominators)
open CycleQ2HodgeEulerContractionRestriction (pull)
open CycleQ2.Cech CycleQ2.Cech.Sections (restrict)
open CycleQ2LogarithmicPullback (Forms)
variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)

abbrev simplexSupport {I : Type} [Fintype I] (v : I → Index) : Finset (Fin 5) :=
  Finset.univ.image (normalIndex ∘ v)
theorem simplexSupport_set {I : Type} [Fintype I] (v : I → Index) :
    (simplexSupport v : Set (Fin 5)) = Set.range (normalIndex ∘ v) := by
  ext j; simp [simplexSupport, Set.mem_range]
abbrev simplexMonoid {I : Type} [Fintype I] (v : I → Index) :=
  denominators (equation φ) (simplexSupport v : Set (Fin 5))
abbrev simplexDivisor {I : Type} [Fintype I] (v : I → Index) := coneDivisor φ (simplexMonoid φ v)
variable {I : Type} [Fintype I] (v : I → Index) (W : (threefold φ).Opens) (h : ∀ a, W ≤ U φ (v a))

theorem open_units (i : Fin 4) (hi : W ≤ CycleQ2GeometricHodgeThreefold.coordinateOpen φ i) :
    ∀ m : simplexMonoid φ v, IsUnit (MvPolynomial.aeval
      (CycleQ2WeightedNativeOverlapSection.coordAt φ i W hi : Fin 5 → Sections φ W)
      (m : CycleQ2WeightedConeChartRestrictions.P k)) := by
  rw [simplexMonoid,simplexSupport_set]
  exact unit_on_commonOpen φ v i W h hi

/-- Reading a cone cochain at an admitted pivot on any common subopen. -/
def readOn (a : I) : simplexDivisor φ v →ₐ[k] Sections φ W :=
  sectionEval φ (simplexMonoid φ v) (v a).1 W ((h a).trans (patch_le_coordinate φ (v a)))
    (open_units φ v W h (v a).1 _)

@[simp] theorem readOn_coord (a : I) (j : Fin 5) :
    readOn φ v W h a (coord φ _ j) =
      CycleQ2WeightedNativeOverlapSection.coordAt φ (v a).1 W ((h a).trans (patch_le_coordinate φ _)) j :=
  sectionEval_coord φ _ _ W _ _ j

/-- Pivots can be changed on every common subopen for each of the three
Euler-projected residue components. -/
theorem readOn_projected_eq (a b : I) (n : ℕ) (ω : Forms k (simplexDivisor φ v) (n+2))
    (e : Expansion φ (simplexMonoid φ v) (n+2) ω) :
    pull (readOn φ v W h b) (n+1) (projected φ _ n ω) =
      pull (readOn φ v W h a) (n+1) (projected φ _ n ω) :=
  projected_eq φ _ _ W _ _ _ _ _ n ω e

/-- Restriction to a smaller open and a larger denominator monoid is
functorial when the same spatial pivot is retained. -/
theorem readOn_comp {J : Type} [Fintype J] (w : J → Index) (V : (threefold φ).Opens)
    (h' : ∀ b, V ≤ U φ (w b)) (hVW : V ≤ W) (a : I) (b : J) (hp : (v a).1 = (w b).1)
    (f : simplexDivisor φ v →ₐ[k] simplexDivisor φ w)
    (hf : ∀ j, f (coord φ _ j) = coord φ _ j) :
    (readOn φ w V h' b).comp f = (restrict (toBase φ) (homOfLE hVW).op).comp (readOn φ v W h a) := by
  apply CycleQ2WeightedConeChartRestrictions.cone_hom_ext φ _
  intro j
  simp only [AlgHom.comp_apply,hf,readOn_coord]
  let hv := (h a).trans (patch_le_coordinate φ (v a))
  let hw := (h' b).trans (patch_le_coordinate φ (w b))
  have he := AlgHom.congr_fun
    (CycleQ2WeightedNativeOverlapSection.restrict_comp_chartAlg φ (v a).1 W hv hVW)
    (CycleQ2HodgeEuler.coordinate φ (v a).1 j)
  simp only [AlgHom.comp_apply, CycleQ2WeightedNativeOverlapSection.chartAlg_coordinate] at he
  simpa only [hp] using he.symm

theorem readOn_pull {J : Type} [Fintype J] (w : J → Index) (V : (threefold φ).Opens)
    (h' : ∀ b, V ≤ U φ (w b)) (hVW : V ≤ W) (a : I) (b : J) (hp : (v a).1 = (w b).1)
    (f : simplexDivisor φ v →ₐ[k] simplexDivisor φ w)
    (hf : ∀ j, f (coord φ _ j) = coord φ _ j) (q : ℕ) (ω : Forms k (simplexDivisor φ v) q) :
    pull (readOn φ w V h' b) q (pull f q ω) =
      pull (restrict (toBase φ) (homOfLE hVW).op) q (pull (readOn φ v W h a) q ω) := by
  refine (CycleQ2LogarithmicPullback.restrict_comp f _ q ω).symm.trans ?_
  rw [readOn_comp φ v W h w V h' hVW a b hp f hf]
  exact CycleQ2LogarithmicPullback.restrict_comp _ _ q ω

variable {p : ℕ}
abbrev read (v : Fin (p+1) → Index) (a : Fin (p+1)) :=
  readOn φ v (intersection (U φ) v) (intersection_le (U φ) v) a

/-- Assemble the actual Kähler-form components in the Čech cochain group. -/
def cochain (p q : ℕ) (ω : ∀ v : Fin (p+1) → Index, Forms k (simplexDivisor φ v) q) :
    Cochain (U φ) (Native.P (toBase φ)) p q :=
  (sectionsEquiv _ _ _).symm (fun v => pull (read φ v 0) q (ω v))

theorem cochain_component (p q : ℕ) (ω : ∀ v : Fin (p+1) → Index, Forms k (simplexDivisor φ v) q)
    (v : Fin (p+1) → Index) :
    component (U φ) (Native.P (toBase φ) q) v (cochain φ p q ω) = pull (read φ v 0) q (ω v) :=
  component_assemble _ _ _ _

/-- Evaluation of the assembled cochain at an actual atlas member uses its
literal scalar extension into that open's own ring of sections. -/
theorem actual_vertex (q : ℕ) (ω : ∀ v : Fin 1 → Index, Forms k (simplexDivisor φ v) q) (a : Index) :
    vertex (U φ) (Native.P (toBase φ) q) a (cochain φ 0 q ω) =
      pull (readOn φ (fun _ : Fin 1 => a) (U φ a) (fun _ => le_rfl) 0) q (ω (fun _ => a)) := by
  let v : Fin 1 → Index := fun _ => a
  let W := intersection (U φ) v
  let h := intersection_le (U φ) v
  let g := singletonLift (U φ) a
  change pull (restrict (toBase φ) g.op) q
    (component (U φ) (Native.P (toBase φ) q) v (cochain φ 0 q ω)) = _
  rw [cochain_component]
  have hs := readOn_comp φ v W h v (U φ a) (fun _ => le_rfl) (leOfHom g) 0 0 rfl
    (AlgHom.id k _) (fun _ => rfl)
  rw [AlgHom.comp_id] at hs
  have hc := CycleQ2LogarithmicPullback.restrict_comp (read φ v 0) (restrict (toBase φ) g.op) q (ω v)
  exact hc.symm.trans (congrArg (fun f => pull f q (ω v)) hs.symm)

end CycleQ2WeightedSectionCochains
end
#print axioms CycleQ2WeightedSectionCochains.readOn_projected_eq
#print axioms CycleQ2WeightedSectionCochains.actual_vertex
