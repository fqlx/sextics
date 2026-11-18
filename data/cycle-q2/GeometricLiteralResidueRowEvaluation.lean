import Proposal.GeometricSeedSectionSheafCurveBinding
import Proposal.GeometricSurfaceNormalCharts

/-!
# Polynomial principal opens on the literal seed surface

The original incidence chart and the surface chart both use the fourth
affine coordinate `(w + X₂²)/Xᵢ²`. Their actual homogeneous localization
equivalence therefore identifies the sections of every affine polynomial.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralResidueRowEvaluation

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceAdjunction CycleQ2SeedSectionCurveRows
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfaceNormalCover
  CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageCocycle

private theorem native_C {S : Type} [CommRing S] [Algebra ℂ S]
    (y : CycleQ2IncidenceUniversalChart.ParameterIndex → S) (i : Fin 4) (c : S) :
    CycleQ2IncidenceDehomogenizedChart.affineEvaluate y i (C c) =
      CycleQ2IncidenceDehomogenizedChart.constants y i c :=
  eval₂Hom_C _ _ _

private theorem native_X {S : Type} [CommRing S] [Algebra ℂ S]
    (y : CycleQ2IncidenceUniversalChart.ParameterIndex → S) (i : Fin 4) (j : Option (Fin 3)) :
    CycleQ2IncidenceDehomogenizedChart.affineEvaluate y i (X j) = (match j with
      | none => CycleQ2IncidenceDehomogenizedChart.coordinateRatio y i (Fin.last 4) +
          CycleQ2IncidenceDehomogenizedChart.coordinateRatio y i (2 : Fin 4).castSucc ^ 2
      | some k => CycleQ2IncidenceDehomogenizedChart.coordinateRatio y i (i.succAbove k).castSucc) :=
  eval₂Hom_X' _ _ _

private theorem localization_affineEvaluate (i : Fin 4) (b : SurfacePoly) :
    literalCartierLocalizationEquiv (X i.castSucc)
        (CycleQ2IncidenceDehomogenizedChart.affineEvaluate seed i b) =
      affineEvaluate 57 1 i b := by
  have hc (c : ℂ) : literalCartierLocalizationEquiv (X i.castSucc)
      (CycleQ2IncidenceDehomogenizedChart.constants seed i c) = constants 57 1 i c :=
    literalCartierLocalizationEquiv_fraction i 0 (C c)
      (isWeightedHomogeneous_C CycleQ2CartierSurfaceGrading.weight c)
  have hv (j : Fin 5) : literalCartierLocalizationEquiv (X i.castSucc)
      (CycleQ2IncidenceDehomogenizedChart.coordinateRatio seed i j) = coordinateRatio 57 1 i j :=
    literalCartierLocalizationEquiv_fraction i _ (X j)
      (isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight j)
  have he : (literalCartierLocalizationEquiv (X i.castSucc)).toRingHom.comp
      (CycleQ2IncidenceDehomogenizedChart.affineEvaluate seed i) = affineEvaluate 57 1 i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact ((congrArg (literalCartierLocalizationEquiv (X i.castSucc)) (native_C seed i c)).trans
        (hc c)).trans (eval₂Hom_C _ _ c).symm
    · intro j
      cases j with
      | none =>
        refine (congrArg (literalCartierLocalizationEquiv (X i.castSucc))
          (native_X seed i none)).trans ?_
        rw [map_add, map_pow, hv, hv]
        simp only [affineEvaluate, eval₂Hom_X']
      | some j =>
        refine ((congrArg (literalCartierLocalizationEquiv (X i.castSucc))
          (native_X seed i (some j))).trans (hv (i.succAbove j).castSucc)).trans ?_
        simp only [affineEvaluate, eval₂Hom_X']
  exact RingHom.congr_fun he b

theorem principalOpen_section {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A]
    [Algebra ℂ A] (e : U.toScheme ≅ Spec (CommRingCat.of A)) (a : A) :
    principalOpen e a = X.basicOpen (chartSection e (Over.mk (𝟙 U)) a) := by
  have ha := ConcreteCategory.congr_hom (chartSection_top e) a
  change chartSection e (Over.mk (𝟙 U)) a =
    U.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) at ha
  rw [principalOpen_image, Scheme.Hom.comp_image, Scheme.Hom.inv_image,
    ← basicOpen_eq_of_affine (R := CommRingCat.of A) a, Scheme.preimage_basicOpen_top, ha,
    ← U.ι_image_basicOpen_topIso_inv]
  rw [Iso.hom_inv_id_apply]

/-- The principal open of an arbitrary chart polynomial is its invertibility
locus for the section transported from the original incidence chart. -/
theorem principalOpen_polynomial (i : Fin 3) (b : SurfacePoly) :
    principalOpen (coordinateAffineChart 57 1 i.succ) (dehomogenizedMap 57 1 i.succ b) =
      Surface.basicOpen (seedCoordinateSectionsEquiv i
        (CycleQ2IncidenceDehomogenizedChart.affineEvaluate seed i.succ b)) := by
  rw [principalOpen_section, coordinate_chartSection_top]
  apply congrArg Surface.basicOpen
  change _ = (Proj.basicOpenIsoAway LiteralCartierGrade _
      (coordinate_mem_grade 57 1 i.succ) (by decide)).hom
    (literalCartierLocalizationEquiv (X i.succ.castSucc)
      (CycleQ2IncidenceDehomogenizedChart.affineEvaluate seed i.succ b))
  rw [localization_affineEvaluate]
  rfl

end CycleQ2LiteralResidueRowEvaluation
end

#print axioms CycleQ2LiteralResidueRowEvaluation.principalOpen_polynomial
