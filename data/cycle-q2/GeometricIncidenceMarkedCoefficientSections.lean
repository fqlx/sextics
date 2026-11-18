import Proposal.GeometricIncidenceCanonicalResidue
import Proposal.GeometricLiteralCanonicalDegreeProjection

/-!
# Marked coordinate cone sections on the projective surface

Evaluate a relative cone section at the retained étale point and take
its weight-zero component on the actual marked surface. This additive
map to ordinary projective sections commutes with every coordinate
restriction and with passage to a smaller open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedCoefficientSections

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEtaleParameter CycleQ2IncidenceCanonicalResidue
  CycleQ2UniversalSurface CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions
  CycleQ2UniversalSurfaceCoefficientMap CycleQ2GeometricSeedNormalizedCoordinates
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceCoordinates CycleQ2GradedLocalizationProjection
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2GeometricProjectiveHOne CycleQ2CartierProjectiveCover
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso

abbrev Face := Finset (Fin 3)
abbrev Local (s : Face) := SurfaceLocal ParameterAlgebra cubic sextic s
abbrev Surface := projectiveSurface (57 : ℂ) 1
abbrev openOf (s : Face) := coordinateIntersection 57 1 s
abbrev coordinate (i : Fin 3) := coordinateOpen 57 1 i
abbrev OS := structureAdditiveSheaf Surface

def changeLocal {h h' : FullCubicTailIndex → ℂ} {F F' : FullSexticTailIndex → ℂ}
    (hh : h = h') (hF : F = F') (s : Face) : SurfaceLocal ℂ h F s ≃+* SurfaceLocal ℂ h' F' s := by
  cases hh
  cases hF
  exact RingEquiv.refl _

private theorem change_apply {h h' : FullCubicTailIndex → ℂ} {F F' : FullSexticTailIndex → ℂ}
    (hh : h = h') (hF : F = F') (s : Face) (x : SurfaceLocal ℂ h F s) :
    changeLocal hh hF s x = (hh ▸ hF ▸ x) := by
  cases hh
  cases hF
  rfl

private theorem change_restrict {h h' : FullCubicTailIndex → ℂ} {F F' : FullSexticTailIndex → ℂ}
    (hh : h = h') (hF : F = F') {s t : Face} (inc : s ⊆ t) (x : SurfaceLocal ℂ h F s) :
    changeLocal hh hF t (restriction ℂ h F inc x) = restriction ℂ h' F' inc (changeLocal hh hF s x) := by
  cases hh
  cases hF
  rfl

private theorem change_polynomial {h h' : FullCubicTailIndex → ℂ} {F F' : FullSexticTailIndex → ℂ}
    (hh : h = h') (hF : F = F') (s : Face) (p : MvPolynomial (Fin 5) ℂ) :
    changeLocal hh hF s (algebraMap _ (SurfaceLocal ℂ h F s) (Ideal.Quotient.mk (surfaceIdeal ℂ h F) p)) =
      algebraMap _ (SurfaceLocal ℂ h' F' s) (Ideal.Quotient.mk (surfaceIdeal ℂ h' F') p) := by
  cases hh
  cases hF
  rfl

/-- The ring map from the relative cone localization to the original marked cone. -/
def markedCone (s : Face) : Local s →+* CoordinateLocal 57 1 s :=
  (normalizedCoordinateEquiv 57 s).symm.toRingHom.comp
    ((changeLocal marked_cubic marked_sextic s).toRingHom.comp (localMap seedMap cubic sextic s))

theorem markedCone_restrict {s t : Face} (inc : s ⊆ t) (x : Local s) :
    markedCone t (restriction ParameterAlgebra cubic sextic inc x) =
      coordinateRestriction 57 1 inc (markedCone s x) := by
  apply (normalizedCoordinateEquiv 57 t).injective
  rw [normalizedCoordinateEquiv_restriction]
  simp only [markedCone, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply, localMap_restriction, change_restrict]

theorem markedCone_polynomial (s : Face) (p : MvPolynomial (Fin 5) ParameterAlgebra) :
    markedCone s (algebraMap _ (Local s) (Ideal.Quotient.mk (surfaceIdeal ParameterAlgebra cubic sextic) p)) =
      algebraMap _ (CoordinateLocal 57 1 s) (quotientMap 57 1 (MvPolynomial.map seedMap p)) := by
  apply (normalizedCoordinateEquiv 57 s).injective
  simp only [markedCone, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply, localMap_algebraMap, surfaceMap_mk, change_polynomial, normalizedCoordinateEquiv_polynomial]

theorem markedCone_residue (x : Local Finset.univ) :
    seedMap (CycleQ2RelativeCanonicalLaurentTrace.residue cubic sextic x) =
      CycleQ2CoordinateCechTrace.localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
        (markedCone Finset.univ x) := by
  rw [← atMark_residue]
  change _ = (CycleQ2GeometricLaurentTop.coordinateLaurent 57 Finset.univ (markedCone Finset.univ x) (2,2)).coeff (fun _ => -1)
  rw [← normalizedCoordinateEquiv_coordinates]
  simp only [markedCone, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply, change_apply]
  rfl

/-- Genuine projective sections obtained by the homogeneous degree-zero projection. -/
def markedSection (s : Face) (hs : s.Nonempty) : Local s →+ Γ(Surface,openOf s) :=
  (coordinateSections 57 1 s hs).toAddMonoidHom.comp
    ((degreeZeroAddHom (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 s)).comp
      (markedCone s).toAddMonoidHom)

theorem markedSection_restrict {s t : Face} (hs : s.Nonempty) (ht : t.Nonempty) (inc : s ⊆ t) (x : Local s) :
    res OS (coordinateIntersection_mono 57 1 inc) (markedSection s hs x) =
      markedSection t ht (restriction ParameterAlgebra cubic sextic inc x) := by
  change Surface.presheaf.map _ (coordinateSections 57 1 s hs
    (degreeZero (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 s) (markedCone s x))) =
    coordinateSections 57 1 t ht (degreeZero (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 t)
      (markedCone t (restriction ParameterAlgebra cubic sextic inc x)))
  rw [coordinateSections_restrict, markedCone_restrict]
  apply congrArg (coordinateSections 57 1 t ht)
  exact (degreeZero_naturality (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 s)
    (coordinateProduct_mem_grade 57 1 (t \ s)) (coordinateProduct_factor 57 1 inc)
    (coordinateProduct_mem_grade 57 1 t) (coordinateRestriction 57 1 inc) (markedCone s x)).symm

theorem le_openOf (s : Face) (W : Surface.Opens) (h : ∀ i ∈ s, W ≤ coordinate i) : W ≤ openOf s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [openOf, coordinateIntersection, coordinateProduct]
  | @insert i s hi ih =>
    change W ≤ Proj.basicOpen (surfaceGrade 57 1) (∏ j ∈ insert i s, coordinateElement 57 1 j)
    rw [Finset.prod_insert hi, Proj.basicOpen_mul]
    exact le_inf (h i (Finset.mem_insert_self _ _)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

def onOpen (s : Face) (hs : s.Nonempty) (W : Surface.Opens) (h : W ≤ openOf s) :
    Local s →+ Γ(Surface,W) :=
  (Surface.presheaf.map (homOfLE h).op).hom.toAddMonoidHom.comp (markedSection s hs)

theorem onOpen_restrict {s t : Face} (hs : s.Nonempty) (ht : t.Nonempty) (inc : s ⊆ t)
    (W : Surface.Opens) (hW : W ≤ openOf t) (x : Local s) :
    onOpen t ht W hW (restriction ParameterAlgebra cubic sextic inc x) =
      onOpen s hs W (hW.trans (coordinateIntersection_mono 57 1 inc)) x := by
  change res OS hW (markedSection t ht _) = res OS _ (markedSection s hs x)
  rw [← markedSection_restrict hs ht inc x]
  exact res_comp OS _ _ _

end CycleQ2IncidenceMarkedCoefficientSections
end

#print axioms CycleQ2IncidenceMarkedCoefficientSections.markedCone_polynomial
#print axioms CycleQ2IncidenceMarkedCoefficientSections.onOpen_restrict
