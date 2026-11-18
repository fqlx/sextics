import Proposal.GeometricHodgeEulerOverlap
import Proposal.GeometricLiteralThreefoldResidueCoordinates

/-!
# The weighted determinant in normalized projective coordinates

Changing the weight-one pivot scales the oriented ambient four-form by the
sixth power of the inverse pivot. The argument applies before imposing the
hypersurface equation, where the four-form is a volume basis. The equation
has the same factor, and its conormal retains that factor on the hypersurface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeEulerContractionTransition

open MvPolynomial CycleQ2HodgeEuler CycleQ2LiteralThreefoldResidueCoordinates
open CycleQ2GeometricIncidenceProj CycleQ2GenericSexticGradient
open scoped KaehlerDifferential TensorProduct

variable {K B : Type} [CommRing K] [CommRing B] [Algebra K B]

private def slot (i : Fin 4) : Option (Fin 3) → Fin 5
  | none => Fin.last 4
  | some a => (i.succAbove a).castSucc

private theorem rotate_slot (i : Fin 4) (a : Fin 4) :
    slot i (finSuccEquiv 3 (finRotate 4 a)) = i.castSucc.succAbove a := by
  fin_cases i <;> fin_cases a <;> rfl

/-- Four-form in the original projective coordinate order with the pivot omitted. -/
def volume (i : Fin 4) (x : Fin 5 → B) : ⋀[B]^4 Ω[B⁄K] :=
  exteriorPower.ιMulti B 4 (fun a => KaehlerDifferential.D K B (x (i.castSucc.succAbove a)))

private theorem volume_rotate [Algebra ℂ B] (i : Fin 4) (x : Fin 5 → B) :
    volume (K := ℂ) i x =
      Equiv.Perm.sign (finRotate 4) • coordinateVolume (x ∘ slot i) := by
  have h := (exteriorPower.ιMulti B 4).map_perm
    (fun a => KaehlerDifferential.D ℂ B (x (slot i (finSuccEquiv 3 a)))) (finRotate 4)
  simpa only [volume, coordinateVolume, Function.comp_def, rotate_slot] using h

private theorem linearValues_slot (i : Fin 4) (x : Fin 5 → B) (hi : x i.castSucc = 1) (a : Fin 4) :
    linearValues i (x ∘ slot i) a = x a.castSucc := by
  refine Fin.succAboveCases i ?_ (fun b => ?_) a <;> simp [linearValues, slot, hi]

def scaledPoint (x : Fin 5 → B) (t : B) (a : Fin 5) := t ^ geometricWeight a * x a

private theorem scaledPoint_slot (i k : Fin 4) (x : Fin 5 → B) (hi : x i.castSucc = 1) (t : B) :
    scaledPoint x t ∘ slot k = changedCoordinate i k (x ∘ slot i) t := by
  funext a
  cases a with
  | none => change t ^ 2 * _ = _ * t^2; exact mul_comm _ _
  | some a =>
    have h := linearValues_slot i x hi (k.succAbove a)
    change t ^ geometricWeight (k.succAbove a).castSucc * x (k.succAbove a).castSucc =
      linearValues i (x ∘ slot i) (k.succAbove a) * t
    have hw (b : Fin 4) : geometricWeight b.castSucc = 1 := by fin_cases b <;> rfl
    rw [hw, pow_one, h, mul_comm]

private theorem volume_change_complex [Algebra ℂ B] (i : Fin 4) (a : Fin 3) (x : Fin 5 → B)
    (hi : x i.castSucc = 1) (t : B) (ht : t * x (i.succAbove a).castSucc = 1) :
    volume (K := ℂ) (i.succAbove a) (scaledPoint x t) =
      ((-1 : B)^(i.val + (i.succAbove a).val)*t^6) • volume (K := ℂ) i x := by
  rw [volume_rotate, scaledPoint_slot i _ x hi t,
    coordinateVolume_change i a (x ∘ slot i) t ht, volume_rotate]
  exact smul_comm _ _ _

private theorem changeBase_volume [Algebra ℂ K] [Algebra ℂ B] [IsScalarTower ℂ K B]
    (i : Fin 4) (x : Fin 5 → B) :
    exteriorPower.map 4 (KaehlerDifferential.map ℂ K B B) (volume (K := ℂ) i x) =
      volume (K := K) i x := by
  simp only [volume, exteriorPower.map_apply_ιMulti, Function.comp_def, KaehlerDifferential.map_D,
    Algebra.algebraMap_self_apply]

theorem volume_change [Algebra ℂ K] [Algebra ℂ B] [IsScalarTower ℂ K B]
    (i : Fin 4) (a : Fin 3) (x : Fin 5 → B) (hi : x i.castSucc = 1)
    (t : B) (ht : t * x (i.succAbove a).castSucc = 1) :
    volume (K := K) (i.succAbove a) (scaledPoint x t) =
      ((-1 : B)^(i.val + (i.succAbove a).val)*t^6) • volume (K := K) i x := by
  have h := congrArg (exteriorPower.map 4 (KaehlerDifferential.map ℂ K B B))
    (volume_change_complex i a x hi t ht)
  simpa only [map_smul, changeBase_volume] using h

def orientedVolume (i : Fin 4) (x : Fin 5 → B) : ⋀[B]^4 Ω[B⁄K] :=
  (-1 : B)^i.val • volume (K := K) i x

theorem orientedVolume_change [Algebra ℂ K] [Algebra ℂ B] [IsScalarTower ℂ K B]
    (i : Fin 4) (a : Fin 3) (x : Fin 5 → B) (hi : x i.castSucc = 1)
    (t : B) (ht : t * x (i.succAbove a).castSucc = 1) :
    orientedVolume (K := K) (i.succAbove a) (scaledPoint x t) =
      t^6 • orientedVolume (K := K) i x := by
  rw [orientedVolume, orientedVolume, volume_change i a x hi t ht, smul_smul, smul_smul, pow_add]
  have h : (-1 : B)^(i.succAbove a).val * (-1 : B)^(i.succAbove a).val = 1 := by
    rw [← mul_pow]; simp
  congr 1
  linear_combination ((-1 : B)^i.val * t^6) * h

theorem dehom_eval (i : Fin 4) (x : Fin 5 → B) (hi : x i.castSucc = 1)
    (p : MvPolynomial (Fin 5) K) :
    aeval (x ∘ i.castSucc.succAbove) (dehom i p) = aeval x p := by
  have h : (aeval (x ∘ i.castSucc.succAbove)).comp (dehom (R := K) i) = aeval x := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.succAboveCases i.castSucc ?_ (fun a => ?_) j <;> simp [hi]
  exact AlgHom.congr_fun h p

theorem equation_change (φ : CoeffRing →+* K) (i k : Fin 4) (x : Fin 5 → B)
    (hi : x i.castSucc = 1) (t : B) (ht : t * x k.castSucc = 1) :
    aeval (scaledPoint x t ∘ k.castSucc.succAbove) (F φ k) =
      t^6 * aeval (x ∘ i.castSucc.succAbove) (F φ i) := by
  let _ : Algebra ℂ K := (φ.comp (C : ℂ →+* CoeffRing)).toAlgebra
  have hw : geometricWeight k.castSucc = 1 := by fin_cases k <;> rfl
  have hk : scaledPoint x t k.castSucc = 1 := by simpa [scaledPoint, hw] using ht
  simp only [F, dehom_eval k _ hk, dehom_eval i _ hi]
  exact CycleQ2IncidenceDehomogenizedChart.weighted_homogeneous_eval_scale
    (algebraMap K B) x t (MvPolynomial.map φ universalF) 6 (family_homogeneous φ)

theorem conormal_change {S : Type} [CommRing S] [Algebra B S] (φ : CoeffRing →+* K)
    (i k : Fin 4) (x : Fin 5 → B) (hi : x i.castSucc = 1) (t : B) (ht : t * x k.castSucc = 1)
    (hz : algebraMap B S (aeval (x ∘ i.castSucc.succAbove) (F φ i)) = 0) :
    (1 : S) ⊗ₜ[B] KaehlerDifferential.D K B (aeval (scaledPoint x t ∘ k.castSucc.succAbove) (F φ k)) =
      (algebraMap B S t)^6 • ((1 : S) ⊗ₜ[B] KaehlerDifferential.D K B
        (aeval (x ∘ i.castSucc.succAbove) (F φ i))) := by
  have hs (a : B) (m : Ω[B⁄K]) : (1 : S) ⊗ₜ[B] (a • m) =
      algebraMap B S a • ((1 : S) ⊗ₜ[B] m) := by
    rw [TensorProduct.tmul_smul]
    exact (IsScalarTower.algebraMap_smul S a _).symm
  rw [equation_change φ i k x hi t ht, Derivation.leibniz, TensorProduct.tmul_add, hs, hs,
    hz, zero_smul, add_zero, map_pow]

end CycleQ2HodgeEulerContractionTransition
end

#print axioms CycleQ2HodgeEulerContractionTransition.volume_change
#print axioms CycleQ2HodgeEulerContractionTransition.conormal_change
