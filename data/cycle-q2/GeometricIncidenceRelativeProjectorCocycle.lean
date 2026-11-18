import Proposal.GeometricIncidenceRelativeProjectorResidue
import Proposal.GeometricProjectorCochainSpecialization

/-!
# Restriction and the cocycle identity for the incidence projector scalar

The chosen local lifts of the image of the actual matrix give one scalar
on every face. Its restriction is the scalar computed in the smaller
open, and its alternating boundary is zero even when each face uses its
own entry certificate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceRelativeProjectorCocycle

open CycleQ2IncidenceRelativeProjectorResidue CycleQ2IncidenceCanonicalResidue
  CycleQ2IncidenceRelativeCechMatrix CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2GeometricUniversalSurfaceFirstOrder
  CycleQ2GeometricRankOneImage CycleQ2GeometricKernelLocalization
  CycleQ2ProjectorCochainSpecialization

private theorem cert (s : Face) (p : s) :
    ∑ ij, restrictedWeights s p ij * matrix s ij.1 ij.2 = 1 := weights_restrict_sum p.val p.property

private def fixed (s : Face) (p i j k : s) : Local s :=
  scalarCochain (reduction s) ((coefficients s).matrixCoefficients (Fin 3)) (matrix s) (matrix_minors s)
    (restrictedWeights s) (cert s) (restrictedProjector s) (restrictedProjector_reduction s) (restrictedWeights s p) i j k

theorem obstruction_fixed (s : Face) (p i j k : s) : obstruction s i j k = fixed s p i j k := by
  apply matrixScalar_certificate_independent (matrix s) (matrix_minors s) (restrictedWeights s i) (restrictedWeights s p)
    (cert s i) (cert s p)
  apply imageCoefficient_left
  exact restrictedProjector_idempotent s

theorem obstruction_closed (s : Face) (i j k l : s) :
    obstruction s j k l - obstruction s i k l + obstruction s i j l - obstruction s i j k = 0 := by
  simp only [obstruction_fixed s i]
  exact obstruction_cocycle s i i j k l

private theorem obstruction_zero_of_defect (s : Face) (i j k : s)
    (hz : CycleQ2GeometricProjectorDefect.defect (restrictedProjector s i)
      (restrictedProjector s j) (restrictedProjector s k) = 0) : obstruction s i j k = 0 := by
  let K := (coefficients s).matrixCoefficients (Fin 3)
  have he : K.cochain (restrictedProjector s)
      (reduced_common_image (reduction s) (matrix s) (matrix_minors s) (restrictedWeights s)
        (cert s) (restrictedProjector s) (restrictedProjector_reduction s)) i j k = 0 := by
    apply K.injective
    rw [K.epsilon_cochain, map_zero, hz]
  change matrixScalar (matrix s) (restrictedWeights s i) (K.cochain _ _ i j k) = 0
  rw [he, map_zero]

theorem obstruction_repeat12 (s : Face) (i k : s) : obstruction s i i k = 0 := by
  apply obstruction_zero_of_defect
  rw [CycleQ2GeometricProjectorDefect.defect, (restrictedProjector_idempotent s i).eq, sub_self]

theorem obstruction_repeat23 (s : Face) (i j : s) : obstruction s i j j = 0 := by
  apply obstruction_zero_of_defect
  rw [CycleQ2GeometricProjectorDefect.defect, mul_assoc, (restrictedProjector_idempotent s j).eq, sub_self]

private abbrev incl {s t : Face} (h : s ⊆ t) (i : s) : t := ⟨i.val,h i.property⟩

theorem weights_map {s t : Face} (h : s ⊆ t) (i : s) (ij : Fin 3 × Fin 3) :
    restriction R cubic sextic h (restrictedWeights s i ij) = restrictedWeights t (incl h i) ij := by
  apply localizedCoordinates_injective R cubic sextic t
  simp only [restrictedWeights, coordinates_restriction]

theorem proj_map {s t : Face} (h : s ⊆ t) (i : s) :
    (restrictedProjector s i).map (localSurfaceRestriction R cubic sextic test h) =
      restrictedProjector t (incl h i) := by
  have he : (localSurfaceRestriction R cubic sextic test h).comp
      (localSurfaceRestriction R cubic sextic test (Finset.singleton_subset_iff.mpr i.property)) =
      localSurfaceRestriction R cubic sextic test (Finset.singleton_subset_iff.mpr (h i.property)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers _)
    apply RingHom.ext
    intro b
    change thickRestriction _ _ (thickRestriction _ _ (algebraMap _ _ b)) = thickRestriction _ _ (algebraMap _ _ b)
    rw [thickRestriction_base, thickRestriction_base, thickRestriction_base]
  ext a b
  exact RingHom.congr_fun he (liftProjector i.val a b)

theorem obstruction_restrict {s t : Face} (h : s ⊆ t) (i j k : s) :
    restriction R cubic sextic h (obstruction s i j k) = obstruction t (incl h i) (incl h j) (incl h k) := by
  let e' := fun n : s => restrictedProjector t (incl h n)
  let w' := fun n : s => restrictedWeights t (incl h n)
  have ar := scalarCochain_map (coefficients s) (coefficients t)
    (localSurfaceRestriction R cubic sextic test h) (restriction R cubic sextic h)
    (localSurfaceEpsilon_restriction R cubic sextic test h)
    (matrix s) (matrix_minors s) (restrictedWeights s) (cert s) (restrictedProjector s) (restrictedProjector_reduction s)
    (matrix t) (matrix_minors t) w' (fun x => cert t (incl h x)) e' (fun x => restrictedProjector_reduction t (incl h x))
    (matrix_restrict h) (proj_map h) (restrictedWeights s i) i j k
  have hw : (fun b => restriction R cubic sextic h (restrictedWeights s i b)) = restrictedWeights t (incl h i) :=
    funext (weights_map h i)
  rw [hw] at ar
  exact ar

end CycleQ2IncidenceRelativeProjectorCocycle
end

#print axioms CycleQ2IncidenceRelativeProjectorCocycle.obstruction_restrict
#print axioms CycleQ2IncidenceRelativeProjectorCocycle.obstruction_closed
