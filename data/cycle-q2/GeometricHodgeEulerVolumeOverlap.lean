import Proposal.GeometricHodgeEulerVolumeChart

/-!
# Agreement of the full chart volumes on the native Euler overlap

Both gradient rows on the double overlap admit Bézout coefficients.
The oriented ambient determinant and the conormal change by the same
sixth power. This identifies the full chart three-forms on the original
overlap ring before any choice of gradient pivot.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeEulerVolumeOverlap

open Module MvPolynomial CycleQ2GenericSexticGradient CycleQ2HodgeEuler
open CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerContractionRestriction
open CycleQ2HodgeEulerContractionTransition (orientedVolume_change)
open CycleQ2HodgeEulerContractionGluing CycleQ2HodgeEulerContractionNative
open CycleQ2HodgeEulerVolumeChart (orientedVolume residue coefficient map_coefficient_identity gradient_smul_residue)
open CycleQ2LiteralThreefoldResidueGluing CycleQ2ExteriorTopBaseChange
open scoped KaehlerDifferential TensorProduct

variable (φ : CoeffRing →+* ℂ) (i : Fin 4) (a : Fin 3)
private abbrev k := i.succAbove a
private abbrev B := overlap φ i (k i a)

local instance targetAlgebra : Algebra (Ambient ℂ a) (B φ i a) := (ambientMap φ i a).toRingHom.toAlgebra
local instance targetTower : IsScalarTower ℂ (Ambient ℂ a) (B φ i a) := IsScalarTower.of_algHom (ambientMap φ i a)

private theorem oldMap : (ambientMap φ i a).comp (aeval (old (K := ℂ) i a)) =
    (sourceMap φ i a).comp (chartMap φ i) := by
  apply MvPolynomial.algHom_ext
  intro d
  simp only [AlgHom.comp_apply, aeval_X, old, Function.comp_apply, point_free, ambientMap_poly]

private theorem newMap : (ambientMap φ i a).comp (aeval (newCoord (K := ℂ) i a)) =
    (overlapMap φ i (k i a)).comp (chartMap φ (k i a)) := by
  apply MvPolynomial.algHom_ext
  intro d
  have h : overlapMap φ i (k i a) (chartMap φ (k i a) (X d)) =
      ratioCoordinate φ i (k i a) ((k i a).castSucc.succAbove d) := by
    simpa only [CycleQ2HodgeEuler.coordinate, dehom_X_succAbove] using
      overlapMap_coordinate φ i (k i a) ((k i a).castSucc.succAbove d)
  simp only [AlgHom.comp_apply, aeval_X, newCoord, Function.comp_apply, ambientMap_scaled, h, k]

private theorem hf : algebraMap (Ambient ℂ a) (B φ i a) (aeval (old (K := ℂ) i a) (F φ i)) = 0 :=
  (AlgHom.congr_fun (oldMap φ i a) (F φ i)).trans (by simp)

private theorem oldEvaluate : evaluate _ _ (hf φ i a) = sourceMap φ i a := by
  apply Ideal.Quotient.algHom_ext
  exact oldMap φ i a

private theorem newEvaluate : evaluate _ _ (new_equation φ i a _ (hf φ i a)) = overlapMap φ i (k i a) := by
  apply Ideal.Quotient.algHom_ext
  exact newMap φ i a

private def base := (ambientBasis (K := ℂ) a).baseChange (B φ i a)
private def changed := restricted (K := ℂ) (S := B φ i a) (newCoord (K := ℂ) i a)
private def factor := (algebraMap (Ambient ℂ a) (B φ i a) (inverse ℂ a)) ^ 6

private theorem base_eq : ⇑(base φ i a) = restricted (K := ℂ) (S := B φ i a) (old (K := ℂ) i a) := by
  funext d
  simp only [base, Basis.baseChange_apply, ambientBasis_apply, restricted, old, Function.comp_apply, point_free]

private theorem determinant :
    (-1 : B φ i a)^(k i a).val * (base φ i a).det (changed φ i a) = factor φ i a * (-1)^i.val := by
  have h := congrArg (topBaseChange (S := B φ i a) (ambientBasis (K := ℂ) a))
    (orientedVolume_change (K := ℂ) i a _ (point_self i a) _ (inverse_mul i a))
  have hr (z : Fin 4 → Ambient ℂ a) : restricted (K := ℂ) (S := B φ i a) z =
      fun d => (1:B φ i a) ⊗ₜ[Ambient ℂ a] KaehlerDifferential.D ℂ (Ambient ℂ a) (z d) := rfl
  have hw : (-1 : B φ i a)^(k i a).val • exteriorPower.ιMulti (B φ i a) 4 (changed φ i a) =
      factor φ i a • ((-1 : B φ i a)^i.val • exteriorPower.ιMulti (B φ i a) 4 (base φ i a)) := by
    rw [base_eq]
    simpa only [factor, k, changed, CycleQ2HodgeEulerContractionTransition.orientedVolume,
      CycleQ2HodgeEulerContractionTransition.volume, topBaseChange_wedge, map_smulₛₗ, map_pow,
      map_neg, map_one, old, newCoord, hr, Function.comp_def] using h
  have hh := congrArg (topCoordinate (base φ i a)) hw
  simp only [map_smul, smul_eq_mul] at hh
  rw [topCoordinate_basis, mul_one, topCoordinate_wedge] at hh
  exact hh

set_option maxHeartbeats 800000 in
theorem overlap_volume (hg : IsUnit (φ gradientOpen)) :
    pull (overlapMap φ i (i.succAbove a)) 3 (orientedVolume φ hg (i.succAbove a)) =
      pull (sourceMap φ i a) 3 (orientedVolume φ hg i) := by
  let fx := sourceMap φ i a
  let fy := overlapMap φ i (k i a)
  let Q := KaehlerDifferential.mapBaseChange ℂ (Ambient ℂ a) (B φ i a)
  let row := fun d => fx (gradientEntry (F φ i) d)
  let row' := fun d => fy (gradientEntry (F φ (k i a)) d)
  have hx : Q ∘ base φ i a = dx (F φ i) fx := by
    change Q ∘ base φ i a = dx _ (sourceMap φ i a)
    rw [base_eq, ← oldEvaluate]
    exact restricted_dx _ _ _
  have hy : Q ∘ changed φ i a = dx (F φ (k i a)) fy := by
    change Q ∘ changed φ i a = dx _ (overlapMap φ i (k i a))
    rw [← newEvaluate]
    exact restricted_dx _ _ _
  have hq : ∑ d, row d • Q (base φ i a d) = 0 := by
    change ∑ d, row d • (Q ∘ base φ i a) d = 0
    rw [hx]
    exact CycleQ2HodgeEulerContractionCharts.gradient_relation (F φ i) fx
  have hn : ∑ d, row' d • changed φ i a d = factor φ i a • ∑ d, row d • base φ i a d := by
    change (∑ d, overlapMap φ i (k i a) (gradientEntry _ d) • restricted (K := ℂ) (S := B φ i a) (newCoord (K := ℂ) i a) d) =
      _ • ∑ d, sourceMap φ i a (gradientEntry _ d) • base φ i a d
    rw [base_eq, ← oldEvaluate, ← newEvaluate, ← restricted_gradient, ← restricted_gradient]
    exact CycleQ2HodgeEulerContractionTransition.conormal_change φ i (k i a) _ (point_self i a) _ (inverse_mul i a) (hf φ i a)
  have hunit : IsUnit (factor φ i a) :=
    ((isUnit_iff_exists_inv.mpr ⟨_, inverse_mul (K := ℂ) i a⟩).map (algebraMap (Ambient ℂ a) (B φ i a))).pow 6
  simp only [orientedVolume, map_smulₛₗ, map_pow, map_neg, map_one]
  apply bezout_residue_change (base φ i a) Q row row' _ _
    (map_coefficient_identity φ hg i fx) (map_coefficient_identity φ hg (k i a) fy)
    (changed φ i a) (factor φ i a) _ _ hunit (determinant φ i a) hn hq
  · intro d; rw [hx]; exact gradient_smul_residue φ hg i fx d
  · intro d; rw [hy]; exact gradient_smul_residue φ hg (k i a) fy d

end CycleQ2HodgeEulerVolumeOverlap
end

#print axioms CycleQ2HodgeEulerVolumeOverlap.overlap_volume
