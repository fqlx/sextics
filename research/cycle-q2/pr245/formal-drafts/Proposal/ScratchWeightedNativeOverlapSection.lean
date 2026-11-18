import Proposal.ScratchCechSchemeSectionAlgebras
import Proposal.GeometricHodgeEulerOverlapBinding
import Proposal.GeometricHodgeEulerTangentCoordinates

/-!
# Restrict the weighted projective overlap to any subopen

The two chart coordinates come from the two projective sections of the same
localized cone. Their maps to a further structure ring are the restrictions
of the native affine chart maps, over the given base ring.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2WeightedNativeOverlapSection

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
  CycleQ2HodgeEulerOverlapBinding CycleQ2HodgeEulerTangentCoordinates
  CycleQ2GeometricAffineChartSections
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeTwistRatios (normalized)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)
open CycleQ2.Cech.Sections (baseMap algebra restrict restrict_baseMap)

variable {R : Type} [CommRing R]

/-- Scalar evaluation on an affine chart above the base agrees with the
scheme's structure morphism on every subopen of the chart. -/
theorem chartSection_scalar {X : Scheme.{0}} {U : X.Opens} {B : Type} [CommRing B]
    [Algebra R B] (e : U.toScheme ≅ Spec (CommRingCat.of B))
    (f : X ⟶ Spec (CommRingCat.of R))
    (hb : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    {W : X.Opens} (hW : W ≤ U) (c : R) :
    chartSection e (Over.mk (homOfLE hW)) (algebraMap R B c) = baseMap f W c := by
  have hr : U.ι.appTop ≫ U.topIso.hom = X.presheaf.map U.leTop.op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)
  have he : U.ι ≫ f = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
    (Iso.hom_inv_id_assoc e _).symm.trans (congrArg (fun m => e.hom ≫ m) hb)
  have ht : CommRingCat.ofHom (algebraMap R B) ≫
      CommRingCat.ofHom (chartSection e (Over.mk (𝟙 U))) = CommRingCat.ofHom (baseMap f U) := by
    rw [chartSection_top]
    change _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.map U.leTop.op
    calc
      _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))).appTop ≫ U.topIso.hom := by
        simp only [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.comp_appTop, Category.assoc]
      _ = _ := by rw [← he, Scheme.Hom.comp_appTop, Category.assoc, hr]
  rw [← chartSection_naturality e
    (Over.homMk (homOfLE hW) : Over.mk (homOfLE hW) ⟶ Over.mk (𝟙 U))]
  exact (congrArg (X.presheaf.map (homOfLE hW).op)
    (ConcreteCategory.congr_hom ht c)).trans (restrict_baseMap f (homOfLE hW).op c)

variable (φ : CoeffRing →+* R) (i k : Fin 4) (W : (threefold φ).Opens)
  (hi : W ≤ coordinateOpen φ i) (hk : W ≤ coordinateOpen φ k)

def chartAlg : letI := algebra (toBase φ) W
    chart φ i →ₐ[R] Γ(threefold φ,W) :=
  letI := algebra (toBase φ) W
  { chartSection (affineChart φ i) (Over.mk (homOfLE hi)) with
    commutes' := chartSection_scalar _ _ (affineChart_overBase φ i) hi }

abbrev coordAt (j : Fin 5) : Γ(threefold φ,W) :=
  normalized φ i (coord φ j) (coord_mem_grade φ j) W hi

theorem chartAlg_coordinate (j : Fin 5) :
    chartAlg φ i W hi (coordinate φ i j) = coordAt φ i W hi j :=
  chartSection_coordinate φ i W hi j

theorem chartAlg_restrict {V : (threefold φ).Opens} (h : V ≤ W) (a : chart φ i) :
    res (threefold φ).sheaf h (chartAlg φ i W hi a) = chartAlg φ i V (h.trans hi) a :=
  chartSection_naturality (affineChart φ i)
    (Over.homMk (homOfLE h) : Over.mk (homOfLE (h.trans hi)) ⟶ Over.mk (homOfLE hi)) a

theorem restrict_comp_chartAlg {V : (threefold φ).Opens} (h : V ≤ W) :
    letI := algebra (toBase φ) W
    letI := algebra (toBase φ) V
    (restrict (toBase φ) (homOfLE h).op).comp (chartAlg φ i W hi) = chartAlg φ i V (h.trans hi) := by
  dsimp only
  apply AlgHom.ext
  exact chartAlg_restrict φ i W hi h

def sectionRingMap : overlap φ i k →+* Γ(threefold φ,W) :=
  (res (threefold φ).sheaf (le_inf hi hk)).comp (overlapSections φ i k).symm.toRingHom

theorem sectionRingMap_left (a : chart φ i) :
    sectionRingMap φ i k W hi hk (algebraMap (chart φ i) (overlap φ i k) a) =
      chartSection (affineChart φ i) (Over.mk (homOfLE hi)) a := by
  have h := overlapSections_restrict φ i k ((chartEquiv φ i).symm a)
  rw [AlgEquiv.apply_symm_apply] at h
  change res (threefold φ).sheaf (le_inf hi hk)
    ((overlapSections φ i k).symm (algebraMap (chart φ i) (overlap φ i k) a)) = _
  rw [← h, RingEquiv.symm_apply_apply, res_comp, chartSection_eq_sectionMap] <;> rfl

theorem sectionRingMap_right (a : chart φ k) :
    sectionRingMap φ i k W hi hk (overlapMap φ i k a) =
      chartSection (affineChart φ k) (Over.mk (homOfLE hk)) a := by
  have h := overlapSections_restrict_other φ i k ((chartEquiv φ k).symm a)
  rw [AlgEquiv.apply_symm_apply] at h
  change res (threefold φ).sheaf (le_inf hi hk)
    ((overlapSections φ i k).symm (overlapMap φ i k a)) = _
  rw [← h, RingEquiv.symm_apply_apply, res_comp, chartSection_eq_sectionMap] <;> rfl

/-- The native overlap section map with scalars from the structure morphism. -/
def nativeMap : letI := algebra (toBase φ) W
    overlap φ i k →ₐ[R] Γ(threefold φ,W) :=
  letI := algebra (toBase φ) W
  { sectionRingMap φ i k W hi hk with
    commutes' := fun c => by
      change sectionRingMap φ i k W hi hk (algebraMap R (overlap φ i k) c) = baseMap (toBase φ) W c
      rw [IsScalarTower.algebraMap_apply R (chart φ i) (overlap φ i k),
        sectionRingMap_left]
      exact chartSection_scalar _ _ (affineChart_overBase φ i) hi c }

theorem nativeMap_chart_left (a : chart φ i) :
    nativeMap φ i k W hi hk (algebraMap (chart φ i) (overlap φ i k) a) =
      chartSection (affineChart φ i) (Over.mk (homOfLE hi)) a :=
  sectionRingMap_left φ i k W hi hk a

theorem nativeMap_chart_right (a : chart φ k) :
    nativeMap φ i k W hi hk (overlapMap φ i k a) =
      chartSection (affineChart φ k) (Over.mk (homOfLE hk)) a :=
  sectionRingMap_right φ i k W hi hk a

theorem nativeMap_localCoordinate (j : Fin 5) :
    nativeMap φ i k W hi hk (localCoordinate φ i k j) =
      normalized φ i (coord φ j) (coord_mem_grade φ j) W hi :=
  (nativeMap_chart_left φ i k W hi hk _).trans (chartSection_coordinate φ i W hi j)

theorem nativeMap_ratioCoordinate (j : Fin 5) :
    nativeMap φ i k W hi hk (ratioCoordinate φ i k j) =
      normalized φ k (coord φ j) (coord_mem_grade φ j) W hk := by
  rw [← overlapMap_coordinate]
  exact (nativeMap_chart_right φ i k W hi hk _).trans (chartSection_coordinate φ k W hk j)

/-- Further restriction agrees on the whole overlap ring. -/
theorem nativeMap_restrict {V : (threefold φ).Opens} (h : V ≤ W) (a : overlap φ i k) :
    res (threefold φ).sheaf h (nativeMap φ i k W hi hk a) =
      nativeMap φ i k V (h.trans hi) (h.trans hk) a :=
  res_comp _ _ _ _

theorem restrict_comp_nativeMap {V : (threefold φ).Opens} (h : V ≤ W) :
    letI := algebra (toBase φ) W
    letI := algebra (toBase φ) V
    (restrict (toBase φ) (homOfLE h).op).comp (nativeMap φ i k W hi hk) =
      nativeMap φ i k V (h.trans hi) (h.trans hk) := by
  dsimp only
  apply AlgHom.ext
  exact nativeMap_restrict φ i k W hi hk h

end CycleQ2WeightedNativeOverlapSection
end
#print axioms CycleQ2WeightedNativeOverlapSection.nativeMap
#print axioms CycleQ2WeightedNativeOverlapSection.restrict_comp_nativeMap
