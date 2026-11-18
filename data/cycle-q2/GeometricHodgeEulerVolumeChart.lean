import Proposal.GeometricHodgeThreefoldGradient
import Proposal.GeometricHodgeEulerContractionNative

/-!
# The moving sextic residue on each full normalized affine chart

The four partials generate one on the smooth parameter open. Their Bézout
coefficients combine the four signed minors into a regular three-form
before localizing in any gradient. Its restriction is the intrinsic
Poincaré residue on every principal gradient chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeEulerVolumeChart

open CycleQ2GenericSexticGradient
open CycleQ2HodgeEuler (chart F)
open CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerContractionRestriction
open CycleQ2LiteralThreefoldResidueMinors (signedOmitted signedOmitted_cross)
open CycleQ2GeometricHodgeThreefold (chartGradient_span)
open CycleQ2ExteriorSectionNaturality (exteriorDifferentialMap)
open scoped KaehlerDifferential

variable {K : Type} [CommRing K] (φ : CoeffRing →+* K) (hg : IsUnit (φ gradientOpen)) (i : Fin 4)

include hg in
theorem exists_bezout : ∃ c : Fin 4 → chart φ i, ∑ j, c j * gradientEntry (F φ i) j = 1 :=
  Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp (chartGradient_span φ hg i))

def coefficient : Fin 4 → chart φ i := (exists_bezout φ hg i).choose

theorem coefficient_identity : ∑ j, coefficient φ hg i j * gradientEntry (F φ i) j = 1 :=
  (exists_bezout φ hg i).choose_spec

def residue : ⋀[chart φ i]^3 Ω[chart φ i⁄K] :=
  ∑ j, coefficient φ hg i j • signedOmitted (chart φ i) (dx (F φ i) (AlgHom.id K (chart φ i))) j

def orientedVolume : ⋀[chart φ i]^3 Ω[chart φ i⁄K] := (-1 : chart φ i)^i.val • residue φ hg i

variable {S : Type} [CommRing S] [Algebra K S] (f : chart φ i →ₐ[K] S)

theorem map_coefficient_identity :
    ∑ j, f (coefficient φ hg i j) * f (gradientEntry (F φ i) j) = 1 := by
  simpa only [map_sum, map_mul, map_one] using congrArg f (coefficient_identity φ hg i)

private theorem pull_signed (j : Fin 4) :
    pull f 3 (signedOmitted (chart φ i) (dx (F φ i) (AlgHom.id K (chart φ i))) j) =
      signedOmitted S (dx (F φ i) f) j := by
  rw [signedOmitted, map_smulₛₗ, pull_wedge]
  simp only [RingHom.map_pow, map_neg, map_one]
  unfold signedOmitted dx
  simp only [Function.comp_apply, pullOne_D, AlgHom.id_apply]
  rfl

theorem gradient_smul_residue (k : Fin 4) :
    f (gradientEntry (F φ i) k) • pull f 3 (residue φ hg i) =
      signedOmitted S (dx (F φ i) f) k := by
  let z := signedOmitted S (dx (F φ i) f)
  have h (j : Fin 4) : f (gradientEntry (F φ i) k) • z j = f (gradientEntry (F φ i) j) • z k :=
    signedOmitted_cross _ _ (gradient_relation (F φ i) f) j k
  rw [residue, map_sum]
  simp only [map_smulₛₗ, pull_signed, Finset.smul_sum]
  change ∑ j, f (gradientEntry (F φ i) k) • (f (coefficient φ hg i j) • z j) = z k
  calc
    _ = ∑ j, (f (coefficient φ hg i j) * f (gradientEntry (F φ i) j)) • z k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_comm (f (gradientEntry (F φ i) k)), h, mul_smul]
    _ = z k := by rw [← Finset.sum_smul, map_coefficient_identity, one_smul]

theorem pull_residue_eq (j : Fin 4) (hj : IsUnit (f (gradientEntry (F φ i) j))) :
    pull f 3 (residue φ hg i) = residueAlong (F φ i) f j hj :=
  (IsUnit.smul_left_cancel hj).mp ((gradient_smul_residue φ hg i f j).trans
    (partial_smul_residueAlong (F φ i) f j hj).symm)

theorem pull_orientedVolume_along (j : Fin 4) (hj : IsUnit (f (gradientEntry (F φ i) j))) :
    pull f 3 (orientedVolume φ hg i) = (-1 : S)^i.val • residueAlong (F φ i) f j hj := by
  simp only [orientedVolume, map_smulₛₗ, map_pow, map_neg, map_one, pull_residue_eq φ hg i f j hj]

set_option maxHeartbeats 800000 in
theorem pull_orientedVolume (j : Fin 4) :
    pull (patchMap (F φ i) j) 3 (orientedVolume φ hg i) = projectiveResidue (F φ i) i j :=
  pull_orientedVolume_along φ hg i (patchMap (F φ i) j) j
    (IsLocalization.Away.algebraMap_isUnit (S := Patch (F φ i) j) (gradientEntry (F φ i) j))

def volumeUnit (j : Fin 4) : (Patch (F φ i) j)ˣ :=
  (-1)^i.val * ((patchUnit (F φ i) j)⁻¹ * (-1)^j.val)

theorem projectiveResidue_eq_frame (j : Fin 4) :
    projectiveResidue (F φ i) i j = (volumeUnit φ i j : Patch (F φ i) j) •
      exteriorPower.ιMulti (Patch (F φ i) j) 3 (basis (F φ i) j) := by
  simp only [projectiveResidue, patchResidue_eq, volumeUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, mul_smul]

theorem exteriorDifferentialMap_eq_pull {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (n : ℕ) : exteriorDifferentialMap f n = pull f n := rfl

end CycleQ2HodgeEulerVolumeChart
end

#print axioms CycleQ2HodgeEulerVolumeChart.gradient_smul_residue
#print axioms CycleQ2HodgeEulerVolumeChart.pull_orientedVolume
