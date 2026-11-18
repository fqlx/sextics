import Proposal.ScratchGenericPoint
import Proposal.ScratchGenericWitness
import Proposal.ScratchGenericPrimitiveClearedTrace
import Proposal.ScratchGenericPointChoice

/-! A finite constant extension and the spatial field have a common finite
extension. A denominator detecting a nonzero spatial polynomial remains
nonzero there. Taking the normalized trace returns its divergence to the
original spatial field. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GeometricGenericPoint

open MvPolynomial CycleQ2FiniteWitness
open CycleQ2MonicWeightedPrimitiveIdentity
open CycleQ2WeightedGenericPrimitiveTrace

theorem descend_finite_certificate
    {A k K E : Type} [CommRing A] [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] [Field E] [Algebra k E] [Module.Finite k E]
    (inclusion : A →+* k) (v₀ : Pol A →+* K)
    (const : ∀ a : A, v₀ (C a) = algebraMap k K (inclusion a))
    (D : Fin 3 → Derivation ℤ K K) (f : Pol A) (hf : v₀ f = 0)
    (hn : v₀ (normal f) ≠ 0)
    (hX : ∀ j i, D j (v₀ (X i)) = v₀ (pderiv j.succ (X i)) -
      v₀ (pderiv j.succ f) / v₀ (normal f) * v₀ (normal (X i)))
    (hconst : ∀ j a, D j (algebraMap k K a) = 0)
    (hsp : AlgebraicIndependent k (fun j : Fin 3 => v₀ (X j.castSucc)))
    (cE : Certificate E (MvPolynomial.map ((algebraMap k E).comp inclusion) f)) :
    ∃ u : Fin 3 → K, ∑ j, D j (u j) = density v₀ f := by
  let P := finitePoint k K E
  let L := P.carrier
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra E L := P.fromCoefficients.toAlgebra
  letI : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq fun a => (P.overBase a).symm
  let e := IsScalarTower.toAlgHom k E L
  let v := coefficientEvaluation e v₀
  let φ := (algebraMap k E).comp inclusion
  have compat : v.comp (MvPolynomial.map φ) = (algebraMap K L).comp v₀ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, v, coefficientEvaluation, eval₂Hom_C]
      change P.fromCoefficients (algebraMap k E (inclusion a)) = algebraMap K L (v₀ (C a))
      rw [const, P.overBase]
    · intro j
      simp only [RingHom.comp_apply, MvPolynomial.map_X, v, coefficientEvaluation, eval₂Hom_X']
  have hzero : v (MvPolynomial.map φ f) = 0 := by
    simpa only [RingHom.comp_apply, hf, map_zero] using RingHom.congr_fun compat f
  let x (j : Fin 3) := algebraMap K L (v₀ (X j.castSucc))
  have hsp' : AlgebraicIndependent E x :=
    CycleQ2GenericSpatialField.extend_spatial (L := L) (E := E) hsp
  have hden : v cE.den ≠ 0 := by
    have hs : v (rename Fin.castSucc cE.spatial) = aeval x cE.spatial :=
      eval₂Hom_rename _ _ _ _
    intro hd
    apply cE.spatial_ne_zero
    apply hsp'.eq_zero_of_aeval_eq_zero
    rw [← hs,cE.spatial_eq,map_add,map_mul,map_mul,hd,hzero,zero_mul,zero_mul,add_zero]
  exact descends_of_finite_constant_point inclusion e v₀ const D hconst f hf hn hX
    cE.den cE.num hden ⟨cE.primitiveFactor,cE.primitive_eq⟩

end CycleQ2GeometricGenericPoint
#print axioms CycleQ2GeometricGenericPoint.descend_finite_certificate
