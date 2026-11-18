import Proposal.GeometricProjectorCompatibleLift
import Proposal.GeometricIncidenceRelativeProjectorSpecialization
import Proposal.GeometricIncidenceRelativeProjectorCocycle

/-!
# The fiber residue obstructs descent of the lifted image line

Compatible transitions between the lifted image summands would produce a
genuine Čech primitive for the specialized obstruction. Multiplication by
the specialized cubic preserves pair sections, so its normalized triple
residue would vanish.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceProjectorLiftObstruction

open CycleQ2IncidenceRelativeProjectorResidue CycleQ2IncidenceRelativeProjectorSpecialization
  CycleQ2IncidenceRelativeCechMatrix CycleQ2IncidenceCanonicalResidue CycleQ2GeometricRankOneImage
  CycleQ2UniversalSurface CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions
  CycleQ2UniversalSurfaceCoefficientMap CycleQ2GeometricUniversalSurfaceFirstOrder
  CycleQ2GeometricKernelLocalization CycleQ2RelativeAmbientTestBaseChange
  CycleQ2ProjectorCompatibleLift CycleQ2RelativeCanonicalLaurentTrace

variable {A : Type} [CommRing A] [Nontrivial A] (f : R →+* A)
private abbrev vertex {s t : Face} (h : s ⊆ t) (i : s) : t := ⟨i.val,h i.property⟩
private abbrev Scalar (s : Face) := SurfaceLocal A (cubicFiber f) (sexticFiber f) s
private abbrev thickRes {s t : Face} (h : s ⊆ t) := localSurfaceRestriction A (cubicFiber f) (sexticFiber f) (testFiber f) h
private abbrev ringRes {s t : Face} (h : s ⊆ t) := restriction A (cubicFiber f) (sexticFiber f) h

theorem project_restrict {s t : Face} (h : s ⊆ t) (i : s) :
    (fiberProjectors f s i).map (thickRes f h) = fiberProjectors f t (vertex h i) := by
  have hr : (deformedMap f t).comp (localSurfaceRestriction R cubic sextic test h) =
      (thickRes f h).comp (deformedMap f s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers _)
    apply RingHom.ext
    intro b
    change thickMap f cubic sextic test t (thickRestriction _ _ (algebraMap _ _ b)) =
      thickRestriction _ _ (thickMap f cubic sextic test s (algebraMap _ _ b))
    rw [thickRestriction_base, thickMap_base, thickMap_base, thickRestriction_base]
  ext a b
  exact (RingHom.congr_fun hr (restrictedProjector s i a b)).symm.trans
    (congrArg (deformedMap f t) (congrArg (fun B : Entries _ => B a b)
      (CycleQ2IncidenceRelativeProjectorCocycle.proj_map h i)))

abbrev OverlapLift (s : Face) (i j : s) :=
  Lift (fiberReduction f s).mapMatrix (fiberProjectors f s) i j

/-- Actual maps of the lifted image summands on the diagram of coordinate overlaps. -/
structure CompatibleLift where
  transition (s : Face) (i j : s) : OverlapLift f s i j
  natural {s t : Face} (h : s ⊆ t) (i j : s) :
    ((transition s i j).hom).map (thickRes f h) = (transition t (vertex h i) (vertex h j)).hom
  compose (s : Face) (i j k : s) :
    (transition s i j).hom * (transition s j k).hom = (transition s i k).hom

private abbrev common (s : Face) := reduced_common_image (fiberReduction f s) (fiberMatrix f s)
  (fiber_minors f s) (fiberWeights f s) (fiber_cert f s) (fiberProjectors f s) (fiberProjector_reduction f s)

variable (L : CompatibleLift f)
private abbrev matrixK (s : Face) := (fiberCoefficients f s).matrixCoefficients (Fin 3)
private abbrev D (s : Face) (i j : s) := difference (matrixK f s) (common f s) (L.transition s i j)
def edgeCorrection (s : Face) (i j : s) : Scalar f s := matrixScalar (fiberMatrix f s) (fiberWeights f s i) (D f L s i j)

private theorem change_cert (s : Face) (i j p : s) : edgeCorrection f L s i j =
    matrixScalar (fiberMatrix f s) (fiberWeights f s p) (D f L s i j) := by
  apply matrixScalar_certificate_independent (fiberMatrix f s) (fiber_minors f s) _ _ (fiber_cert f s i) (fiber_cert f s p)
  rw [← fiberProjector_reduction f s i]
  exact difference_left (matrixK f s) (fun n => (fiberProjector_idempotent f s n).eq)
    (common f s) (L.transition s i j)

theorem face_boundary (s : Face) (i j k : s) :
    fiberObstruction f s i j k = edgeCorrection f L s j k - edgeCorrection f L s i k + edgeCorrection f L s i j := by
  rw [change_cert f L s j k i]
  exact scalar_boundary (fiberReduction f s) (matrixK f s) (fiberMatrix f s) (fiber_minors f s)
    (fiberWeights f s) (fiber_cert f s) (fiberProjectors f s) (fun n => (fiberProjector_idempotent f s n).eq)
    (fiberProjector_reduction f s) i j k _ _ _ (L.compose s i j k) (fiberWeights f s i)

theorem edgeCorrection_restrict {s t : Face} (h : s ⊆ t) (i j : s) :
    ringRes f h (edgeCorrection f L s i j) = edgeCorrection f L t (vertex h i) (vertex h j) := by
  have hM : (fiberMatrix f s).map (ringRes f h) = fiberMatrix f t := by
    ext a b
    exact (localMap_restriction f cubic sextic h _).symm.trans
      (congrArg (closedMap f t) (congrArg (fun B : Entries _ => B a b) (matrix_restrict h)))
  have hw : (fun b => ringRes f h (fiberWeights f s i b)) = fiberWeights f t (vertex h i) := by
    funext b
    exact (localMap_restriction f cubic sextic h _).symm.trans
      (congrArg (closedMap f t) (CycleQ2IncidenceRelativeProjectorCocycle.weights_map h i b))
  unfold edgeCorrection
  rw [matrixScalar_map, hM, hw]
  apply congrArg (matrixScalar _ _)
  apply (matrixK f t).injective
  have hx : (matrixK f t).epsilon ((D f L s i j).map (ringRes f h)) =
      ((matrixK f s).epsilon (D f L s i j)).map (thickRes f h) := by
    ext a b
    exact (localSurfaceEpsilon_restriction A (cubicFiber f) (sexticFiber f) (testFiber f) h _).symm
  rw [hx, epsilon_difference, epsilon_difference]
  change (thickRes f h).mapMatrix (_ * _ - _) = _
  rw [map_sub, map_mul]
  exact congrArg₂ (· - ·) (congrArg₂ (· * ·) (project_restrict f h i) (project_restrict f h j)) (L.natural h i j)

private def multiplier (s : Face) : Scalar f s := algebraMap (SurfaceRing A (cubicFiber f) (sexticFiber f)) _
  (Ideal.Quotient.mk _ (MvPolynomial.map f velocityCubic))

private theorem weighted_restrict {s t : Face} (h : s ⊆ t) (i j : s) :
    ringRes f h (multiplier f s * edgeCorrection f L s i j) =
      multiplier f t * edgeCorrection f L t (vertex h i) (vertex h j) := by
  rw [map_mul, edgeCorrection_restrict, multiplier, restriction_algebraMap]
  rfl

theorem residue_zero_of_lift : f regularCoefficient = 0 := by
  let s₀₁ : Face := {0,1}
  let s₀₂ : Face := {0,2}
  let s₁₂ : Face := {1,2}
  let a := multiplier f s₀₁ * edgeCorrection f L s₀₁ ⟨0,by decide⟩ ⟨1,by decide⟩
  let b := multiplier f s₀₂ * edgeCorrection f L s₀₂ ⟨0,by decide⟩ ⟨2,by decide⟩
  let c := multiplier f s₁₂ * edgeCorrection f L s₁₂ ⟨1,by decide⟩ ⟨2,by decide⟩
  rw [← fiber_residue]
  have h := residue_boundary (cubicFiber f) (sexticFiber f) a b c
  change residue _ _ (ringRes f _ c - ringRes f _ b + ringRes f _ a) = 0 at h
  dsimp only [a,b,c] at h
  rw [weighted_restrict, weighted_restrict, weighted_restrict, ← mul_sub, ← mul_add] at h
  change residue _ _ (multiplier f Finset.univ * fiberObstruction f Finset.univ _ _ _) = 0
  rw [face_boundary f L]
  exact h

theorem no_compatible_lift (h : f regularCoefficient ≠ 0) : IsEmpty (CompatibleLift f) :=
  ⟨fun L => h (residue_zero_of_lift f L)⟩

end CycleQ2IncidenceProjectorLiftObstruction
end

#print axioms CycleQ2IncidenceProjectorLiftObstruction.no_compatible_lift
