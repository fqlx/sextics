import Proposal.GeometricHodgeEulerContractionGluing

/-!
# Oriented residues through the moving family's overlap maps

Both normalized chart maps factor through the original Euler overlap.
The restriction of the intrinsic three-form along these maps agrees on
every further overlap where the two independently chosen gradients are units.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeEulerContractionNative

open MvPolynomial CycleQ2GenericSexticGradient CycleQ2HodgeEuler
open CycleQ2HodgeEulerChartDerivations CycleQ2HodgeEulerContractionCharts
open CycleQ2HodgeEulerContractionGluing CycleQ2HodgeEulerContractionTransition
open CycleQ2GeometricIncidenceProj

variable {K : Type} [CommRing K] (φ : CoeffRing →+* K) (i : Fin 4) (a : Fin 3)

abbrev sourceMap : chart φ i →ₐ[K] overlap φ i (i.succAbove a) :=
  IsScalarTower.toAlgHom K _ _

private theorem pivot_eq :
    sourceMap φ i a (chartMap φ i (X a.castSucc)) = localCoordinate φ i (i.succAbove a) (i.succAbove a).castSucc := by
  have h : (i.succAbove a).castSucc = i.castSucc.succAbove a.castSucc := by
    fin_cases i <;> fin_cases a <;> rfl
  simp only [localCoordinate, coordinate, h, dehom_X_succAbove]
  rfl

def ambientMap : Ambient K a →ₐ[K] overlap φ i (i.succAbove a) :=
  IsLocalization.Away.liftAlgHom (X a.castSucc : Poly K) (f := (sourceMap φ i a).comp (chartMap φ i))
    (by
      change IsUnit (sourceMap φ i a (chartMap φ i (X a.castSucc)))
      rw [pivot_eq]
      exact isUnit_iff_exists_inv.mpr ⟨_, localCoordinate_mul_invPivot φ i _⟩)

@[simp] theorem ambientMap_poly (p : Poly K) :
    ambientMap φ i a (algebraMap (Poly K) _ p) = sourceMap φ i a (chartMap φ i p) :=
  IsLocalization.lift_eq _ _

theorem ambientMap_point (j : Fin 5) :
    ambientMap φ i a (point i a j) = localCoordinate φ i (i.succAbove a) j := by
  refine Fin.succAboveCases i.castSucc ?_ (fun d => ?_) j
  · simp [point_self, localCoordinate, coordinate]
  · simp only [point_free, ambientMap_poly, localCoordinate, coordinate, dehom_X_succAbove]
    rfl

theorem ambientMap_inverse : ambientMap φ i a (inverse K a) = invPivot φ i (i.succAbove a) := by
  have h := congrArg (ambientMap φ i a) (inverse_mul (K := K) i a)
  rw [map_mul, ambientMap_point, map_one] at h
  have hunit : IsUnit (localCoordinate φ i (i.succAbove a) (i.succAbove a).castSucc) :=
    isUnit_iff_exists_inv.mpr ⟨_, localCoordinate_mul_invPivot φ i _⟩
  apply hunit.mul_right_cancel
  exact h.trans ((mul_comm _ _).trans (localCoordinate_mul_invPivot φ i _)).symm

theorem ambientMap_scaled (j : Fin 5) :
    ambientMap φ i a (scaledPoint (point i a) (inverse K a) j) = ratioCoordinate φ i (i.succAbove a) j := by
  rw [scaledPoint, map_mul, map_pow, ambientMap_inverse, ambientMap_point, ratioCoordinate]

set_option maxHeartbeats 800000 in
theorem overlap_residue {S : Type} [CommRing S] [Algebra K S] (f : overlap φ i (i.succAbove a) →ₐ[K] S)
    (j l : Fin 4)
    (hj : IsUnit ((f.comp (sourceMap φ i a)) (gradientEntry (F φ i) j)))
    (hl : IsUnit ((f.comp (overlapMap φ i (i.succAbove a))) (gradientEntry (F φ (i.succAbove a)) l))) :
    (-1 : S)^(i.succAbove a).val • residueAlong _ (f.comp (overlapMap φ i (i.succAbove a))) l hl =
      (-1 : S)^i.val • residueAlong _ (f.comp (sourceMap φ i a)) j hj := by
  let k := i.succAbove a
  let G := f.comp (ambientMap φ i a)
  let _ : Algebra (Ambient K a) S := G.toRingHom.toAlgebra
  let _ : IsScalarTower K (Ambient K a) S := IsScalarTower.of_algHom G
  have hOld : G.comp (aeval (old (K := K) i a)) = (f.comp (sourceMap φ i a)).comp (chartMap φ i) := by
    apply MvPolynomial.algHom_ext
    intro d
    simp only [AlgHom.comp_apply, aeval_X, G, old, Function.comp_apply, point_free, ambientMap_poly]
  have hf : algebraMap (Ambient K a) S (aeval (old (K := K) i a) (F φ i)) = 0 := by
    have h := AlgHom.congr_fun hOld (F φ i)
    change G (aeval (old (K := K) i a) (F φ i)) = _
    exact h.trans (by simp)
  have hfx : evaluate _ _ hf = f.comp (sourceMap φ i a) := by
    apply Ideal.Quotient.algHom_ext
    exact hOld
  have hNew : G.comp (aeval (newCoord (K := K) i a)) = (f.comp (overlapMap φ i k)).comp (chartMap φ k) := by
    apply MvPolynomial.algHom_ext
    intro d
    have h : overlapMap φ i k (chartMap φ k (X d)) = ratioCoordinate φ i k (k.castSucc.succAbove d) := by
      simpa only [CycleQ2HodgeEuler.coordinate, dehom_X_succAbove] using
        overlapMap_coordinate φ i k (k.castSucc.succAbove d)
    simp only [AlgHom.comp_apply, aeval_X, G, newCoord, Function.comp_apply, ambientMap_scaled, h, k]
  have hfy : evaluate _ _ (new_equation φ i a S hf) = f.comp (overlapMap φ i k) := by
    apply Ideal.Quotient.algHom_ext
    exact hNew
  have h1 : IsUnit (evaluate _ _ hf (gradientEntry _ j)) := hfx.symm ▸ hj
  have h2 : IsUnit (evaluate _ _ (new_equation φ i a S hf) (gradientEntry _ l)) := hfy.symm ▸ hl
  have h := residue_change φ i a S hf j l h1 h2
  simpa only [hfx, hfy] using h

end CycleQ2HodgeEulerContractionNative
end

#print axioms CycleQ2HodgeEulerContractionNative.overlap_residue
