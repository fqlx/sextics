import Proposal.GeometricIncidenceMarkedCoefficientSections
import Proposal.GeometricIncidenceRelativeProjectorResidue
import Proposal.GeometricRelativeAmbientTestBaseChange

/-!
# Specialization to the marked ambient-test deformation

The relative deformation of the incidence equations by the scaled test
specializes to the original marked equation and its original infinitesimal
test. The map commutes with reduction, the epsilon kernel, and coordinate
restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedDeformationMap

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceCanonicalResidue CycleQ2IncidenceRelativeProjectorResidue
  CycleQ2GeometricSeedNormalizedCoordinates CycleQ2GeometricUniversalSurfaceFirstOrder
  CycleQ2UniversalSurfaceCoefficientMap CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2GeometricKernelLocalization CycleQ2RelativeAmbientTestBaseChange
  CycleQ2GeometricSurfaceFirstOrder CycleQ2NormalConnecting
  CycleQ2IncidenceMarkedCoefficientSections

private abbrev Face := Finset (Fin 3)
abbrev MarkedThick := LocalSurfaceDeformation ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA
abbrev markedReduction := localSurfaceReduction ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA
abbrev markedCoefficients := localSurfaceCoefficients ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA

private def changeThick {h h' : FullCubicTailIndex → ℂ} {F F' : FullSexticTailIndex → ℂ}
    {T T' : MvPolynomial (Fin 5) ℂ} (hh : h = h') (hF : F = F') (hT : T = T') (s : Face) :
    LocalSurfaceDeformation ℂ h F T s ≃+* LocalSurfaceDeformation ℂ h' F' T' s := by
  cases hh
  cases hF
  cases hT
  exact RingEquiv.refl _

private theorem changeThick_reduce {h h' : FullCubicTailIndex → ℂ} {F F' : FullSexticTailIndex → ℂ}
    {T T' : MvPolynomial (Fin 5) ℂ} (hh : h = h') (hF : F = F') (hT : T = T') (s : Face)
    (z : LocalSurfaceDeformation ℂ h F T s) :
    localSurfaceReduction ℂ h' F' T' s (changeThick hh hF hT s z) =
      changeLocal hh hF s (localSurfaceReduction ℂ h F T s z) := by cases hh; cases hF; cases hT; rfl

private theorem changeThick_epsilon {h h' : FullCubicTailIndex → ℂ} {F F' : FullSexticTailIndex → ℂ}
    {T T' : MvPolynomial (Fin 5) ℂ} (hh : h = h') (hF : F = F') (hT : T = T') (s : Face)
    (x : SurfaceLocal ℂ h F s) :
    changeThick hh hF hT s ((localSurfaceCoefficients ℂ h F T s).epsilon x) =
      (localSurfaceCoefficients ℂ h' F' T' s).epsilon (changeLocal hh hF s x) := by cases hh; cases hF; cases hT; rfl

private theorem changeThick_restrict {h h' : FullCubicTailIndex → ℂ} {F F' : FullSexticTailIndex → ℂ}
    {T T' : MvPolynomial (Fin 5) ℂ} (hh : h = h') (hF : F = F') (hT : T = T') {s t : Face} (inc : s ⊆ t)
    (x : LocalSurfaceDeformation ℂ h F T s) :
    changeThick hh hF hT t (localSurfaceRestriction ℂ h F T inc x) =
      localSurfaceRestriction ℂ h' F' T' inc (changeThick hh hF hT s x) := by cases hh; cases hF; cases hT; rfl

def thickAtMark (s : Face) : Thick s →+* MarkedThick s :=
  (changeThick marked_cubic marked_sextic test_marked s).toRingHom.comp
    (thickMap seedMap cubic sextic test s)

def closedAtMark (s : Face) : CycleQ2IncidenceMarkedCoefficientSections.Local s →+* NormalizedLocal 57 s :=
  (changeLocal marked_cubic marked_sextic s).toRingHom.comp (localMap seedMap cubic sextic s)

theorem closedAtMark_eq (s : Face) (x : CycleQ2IncidenceMarkedCoefficientSections.Local s) :
    closedAtMark s x = normalizedCoordinateEquiv 57 s (markedCone s x) :=
  ((normalizedCoordinateEquiv 57 s).apply_symm_apply (closedAtMark s x)).symm

theorem closedAtMark_restrict {s t : Face} (inc : s ⊆ t) (x : CycleQ2IncidenceMarkedCoefficientSections.Local s) :
    closedAtMark t (CycleQ2UniversalSurfaceRestrictions.restriction R cubic sextic inc x) =
      CycleQ2UniversalSurfaceRestrictions.restriction ℂ (cubicCoefficients 57) (sexticCoefficients 57) inc
        (closedAtMark s x) := by
  rw [closedAtMark_eq, markedCone_restrict, normalizedCoordinateEquiv_restriction, ← closedAtMark_eq]

theorem thickAtMark_reduce (s : Face) (x : Thick s) :
    markedReduction s (thickAtMark s x) = closedAtMark s (reduction s x) := by
  change _ (changeThick _ _ _ _ _) = changeLocal _ _ _ _
  rw [changeThick_reduce, thickMap_reduce]

theorem thickAtMark_epsilon (s : Face) (x : CycleQ2IncidenceMarkedCoefficientSections.Local s) :
    thickAtMark s ((coefficients s).epsilon x) = (markedCoefficients s).epsilon (closedAtMark s x) := by
  change changeThick _ _ _ s (thickMap seedMap cubic sextic test s _) = _
  rw [thickMap_epsilon, changeThick_epsilon]
  rfl

theorem thickAtMark_restrict {s t : Face} (inc : s ⊆ t) (x : Thick s) :
    thickAtMark t (localSurfaceRestriction R cubic sextic test inc x) =
      localSurfaceRestriction ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA inc
        (thickAtMark s x) := by
  let h := fun i => seedMap (cubic i)
  let F := fun i => seedMap (sextic i)
  let T := MvPolynomial.map seedMap test
  have hn : (thickMap seedMap cubic sextic test t).comp (localSurfaceRestriction R cubic sextic test inc) =
      (localSurfaceRestriction ℂ h F T inc).comp (thickMap seedMap cubic sextic test s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers _)
    apply RingHom.ext
    intro b
    change thickMap seedMap cubic sextic test t (thickRestriction _ _ (algebraMap _ _ b)) =
      thickRestriction _ _ (thickMap seedMap cubic sextic test s (algebraMap _ _ b))
    rw [thickRestriction_base, thickMap_base, thickMap_base, thickRestriction_base]
  change changeThick _ _ _ t ((thickMap seedMap cubic sextic test t).comp _ x) = _
  rw [hn]
  exact changeThick_restrict marked_cubic marked_sextic test_marked inc _

end CycleQ2IncidenceMarkedDeformationMap
end

#print axioms CycleQ2IncidenceMarkedDeformationMap.thickAtMark_restrict
#print axioms CycleQ2IncidenceMarkedDeformationMap.thickAtMark_epsilon
