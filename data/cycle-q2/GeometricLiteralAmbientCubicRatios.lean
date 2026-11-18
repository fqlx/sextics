import Proposal.GeometricHodgeThreefoldIncidenceSections
import Proposal.GeometricHodgeThreefoldTwist
import Proposal.GeometricHodgeAtlasRestriction
import Proposal.GeometricLiteralThreefoldOrbitAction
import Proposal.GeometricLiteralAbelJacobiQCoordinates
import Proposal.GeometricFullSurfaceResidueCover
import Proposal.GeometricLiteralCoordinateTwist

/-!
# The cubic transition on the original residue surface

The three residue charts are the inverse images of the ambient charts for the coordinates
X₁, X₂ and X₃. The graded quotient defining the surface preserves the numerator and
denominator of each homogeneous fraction. Thus its pulled cubic transition is the cube
of the coordinate ratio in the original residue frame.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 5000
set_option maxHeartbeats 900000

noncomputable section
namespace CycleQ2LiteralAmbientCubicRatios

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2LiteralAmbientCylinder (point Native)
open CycleQ2SeedTrace (WeightedPoly)
open CycleQ2GeometricSurfaceOverlap (coordinateDen)
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2LiteralThreefoldOrbitAction
  CycleQ2IncidenceFamilyContainment CycleQ2LiteralAbelJacobiQCoordinates
  CycleQ2CartierProjectiveCover CycleQ2CartierSurfaceGrading
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SurfaceCoordinateSections
  CycleQ2FullSurfaceJacobianCover CycleQ2HodgeAtlasLine CycleQ2HodgeThreefoldTwist
  CycleQ2GeometricIncidenceProj

private abbrev Z := threefold (sexticEval point)
private abbrev D := projectiveSurface 57 1
abbrev embedding : D ⟶ Z := surfaceToNative ≫ (nativeIso point).inv

private abbrev surfaceCocycle : Transition (fun i : Fin 4 => embedding ⁻¹ᵁ coordinateOpen (sexticEval point) i) :=
  @pulled D Z embedding (Fin 4) (coordinateOpen (sexticEval point)) (cocycle (sexticEval point) 3)

private theorem native_open (i : Fin 4) :
    surfaceToNative ⁻¹ᵁ nativeOpen point i = coordinatePatch 57 1 i.castSucc := by
  change (Proj.map toTraceGraded trace_irrelevant) ⁻¹ᵁ Proj.basicOpen _ _ = _
  rw [Proj.map_preimage_basicOpen]
  rfl

private theorem inv_open {Y Z : Scheme} (e : Y ≅ Z) (U : Z.Opens) (V : Y.Opens)
    (h : e.hom ⁻¹ᵁ U = V) : e.inv ⁻¹ᵁ V = U := by
  subst V
  exact congrArg (fun f : Z ⟶ Z => f ⁻¹ᵁ U) e.inv_hom_id

private theorem native_inv_open (i : Fin 4) :
    (nativeIso point).inv ⁻¹ᵁ coordinateOpen (sexticEval point) i = nativeOpen point i :=
  @inv_open Z Native (nativeIso point) (nativeOpen point i) (coordinateOpen (sexticEval point) i)
    (nativeIso_preimage point i)

private theorem model_open (i : Fin 4) :
    embedding ⁻¹ᵁ coordinateOpen (sexticEval point) i = coordinatePatch 57 1 i.castSucc := by
  unfold embedding
  rw [Scheme.Hom.comp_preimage, native_inv_open, native_open]

theorem model_surface_open (i : Fin 3) :
    embedding ⁻¹ᵁ coordinateOpen (sexticEval point) (projectiveIndex i) =
      CycleQ2FullSurfaceResidueCover.coordinateOpen i :=
  model_open _

private theorem native_fraction (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n) (W : D.Opens)
    (hW : W ≤ coordinatePatch 57 1 i.castSucc) :
    surfaceToNative.appLE (nativeOpen point i) W (hW.trans (native_open i).ge)
      (nativeNormalized point i n p hp) = coordinatePolynomialSection 57 1 i W hW p := by
  let u := sexticX point i
  let a := sexticFraction point i n p hp
  have ht := ConcreteCategory.congr_hom
    (Proj.awayToSection_comp_appLE toTraceGraded trace_irrelevant (sexticX_mem point i)) a
  change surfaceToNative.appLE (nativeOpen point i) (coordinatePatch 57 1 i.castSucc)
    (native_open i).ge (nativeNormalized point i n p hp) =
    Proj.awayToSection (surfaceGrade 57 1) (coordinateDen 57 1 i) (Away.map toTraceGraded u a) at ht
  have hm : Away.map toTraceGraded u a = homogeneousFraction 57 1 i n p hp := by
    change Away.map toTraceGraded u (Away.mk _ _ n _ _) = _
    rw [Away.map_mk]
    rfl
  rw [hm] at ht
  rw [coordinatePolynomialSection_fraction 57 1 i W hW n p hp]
  have hrs := ConcreteCategory.congr_hom (surfaceToNative.appLE_map (native_open i).ge
    (homOfLE hW).op) (nativeNormalized point i n p hp)
  exact hrs.symm.trans (congrArg (D.presheaf.map (homOfLE hW).op) ht)

private theorem app_congr {X Y : Scheme} {f g : X ⟶ Y} (e : f = g)
    (V : Y.Opens) (W : X.Opens) (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) :
    f.appLE V W hf = g.appLE V W hg := by subst g; rfl

private theorem cancel_iso_app {X Y Z : Scheme} (f : X ⟶ Z) (e : Y ≅ Z)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (hV : V ≤ e.hom ⁻¹ᵁ U)
    (hW : W ≤ (f ≫ e.inv) ⁻¹ᵁ V) (k : W ≤ f ⁻¹ᵁ U) :
    e.hom.appLE U V hV ≫ (f ≫ e.inv).appLE V W hW = f.appLE U W k :=
  (Scheme.Hom.appLE_comp_appLE (f ≫ e.inv) e.hom U V W hV hW).trans
    (app_congr (show (f ≫ e.inv) ≫ e.hom = f by simp) U W _ k)

/-- Pulling a homogeneous polynomial divided by Xᵢⁿ to a surface subopen gives its
original dehomogenized chart section. -/
theorem surface_normalized (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n)
    (V : Z.Opens) (hi : V ≤ coordinateOpen (sexticEval point) i)
    (W : D.Opens) (hW : W ≤ embedding ⁻¹ᵁ V) :
    embedding.appLE V W hW
      (CycleQ2HodgeTwistRatios.normalized (sexticEval point) i (n := n) (quotient (sexticEval point) p)
        (quotient_mem_grade (sexticEval point) (n := n) p hp) V hi) =
    coordinatePolynomialSection 57 1 i W
      ((hW.trans (embedding.preimage_mono hi)).trans (model_open i).le) p := by
  let k := (hW.trans (embedding.preimage_mono hi)).trans (model_open i).le
  let H := nativeNormalized point i n p hp
  have he := nativeIso_normalized point i n p hp V hi
  exact (congrArg (embedding.appLE V W hW) he.symm).trans
    ((ConcreteCategory.congr_hom (@cancel_iso_app D Z Native surfaceToNative (nativeIso point)
      (nativeOpen point i) V W (hi.trans (nativeIso_preimage point i).ge) hW
      (k.trans (native_open i).ge)) H).trans (native_fraction i n p hp W k))

private theorem pull_cubic_transition {R : Type} [CommRing R]
    (φ : CycleQ2GenericSexticGradient.CoeffRing →+* R) {S : Scheme.{0}}
    (f : S ⟶ threefold φ) (i j : Fin 4) (V : (threefold φ).Opens) (W : S.Opens)
    (hi : V ≤ coordinateOpen φ i) (hj : V ≤ coordinateOpen φ j) (hW : W ≤ f ⁻¹ᵁ V) :
    ((pulled f (cocycle φ 3)).unit i j W (hW.trans (f.preimage_mono hi))
      (hW.trans (f.preimage_mono hj))).val = (f.appLE V W hW (CycleQ2HodgeTwistRatios.ratio φ i j V hi))^3 := by
  rw [pulled_unit_on f _ i j V W hi hj hW]
  change f.appLE V W hW ((CycleQ2HodgeTwistRatios.transition φ i j V hi hj ^ ((3 : ℕ) : ℤ)).val) = _
  simp only [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, CycleQ2HodgeTwistRatios.transition]

/-- In the original canonical frames the pulled cubic line changes by (Xⱼ/Xᵢ)³. -/
theorem surface_cubic_transition (i j : Fin 3) (W : D.Opens)
    (hi : W ≤ CycleQ2FullSurfaceResidueCover.coordinateOpen i)
    (hj : W ≤ CycleQ2FullSurfaceResidueCover.coordinateOpen j) :
    (surfaceCocycle.unit (projectiveIndex i) (projectiveIndex j)
      W (hi.trans (model_surface_open i).ge) (hj.trans (model_surface_open j).ge)).val =
    (coordinatePolynomialSection 57 1 (projectiveIndex i) W hi
      (X (projectiveIndex j).castSucc)) ^ 3 := by
  let V := coordinateOpen (sexticEval point) (projectiveIndex i) ⊓
    coordinateOpen (sexticEval point) (projectiveIndex j)
  have hW : W ≤ embedding ⁻¹ᵁ V :=
    le_inf (hi.trans (model_surface_open i).ge) (hj.trans (model_surface_open j).ge)
  refine (pull_cubic_transition (sexticEval point) embedding (projectiveIndex i) (projectiveIndex j)
    V W inf_le_left inf_le_right hW).trans ?_
  apply congrArg (· ^ (3 : ℕ))
  have hp : (X (projectiveIndex j).castSucc : WeightedPoly).IsWeightedHomogeneous geometricWeight 1 := by
    simpa only [CycleQ2SeedFermatProj.geometricWeight_castSucc] using
      isWeightedHomogeneous_X ℂ geometricWeight (projectiveIndex j).castSucc
  exact surface_normalized _ 1 _ hp V inf_le_left W hW

/-- The same unit is the transition used to glue the existing surface twist. -/
theorem surface_scalarUnit (i j : Fin 3) (W : D.Opens)
    (hi : W ≤ CycleQ2FullSurfaceResidueCover.coordinateOpen i)
    (hj : W ≤ CycleQ2FullSurfaceResidueCover.coordinateOpen j) :
    surfaceCocycle.unit (projectiveIndex i) (projectiveIndex j)
      W (hi.trans (model_surface_open i).ge) (hj.trans (model_surface_open j).ge) =
    CycleQ2LiteralMovingIdealExact.scalarUnit 3 i j W hi hj := by
  have h : CycleQ2LiteralMovingIdealExact.scalarUnit 3 i j W hi hj =
      CycleQ2SeedProjectiveImageCocycle.transitionUnit j i W hj hi ^ (3 : ℕ) := by
    rw [CycleQ2LiteralMovingIdealExact.scalarUnit, CycleQ2SeedProjectiveImageCocycle.transitionUnit_symm i j]
    simp
  apply Units.ext
  rw [h, Units.val_pow_eq_pow_val]
  exact surface_cubic_transition i j W hi hj

end CycleQ2LiteralAmbientCubicRatios
end

#print axioms CycleQ2LiteralAmbientCubicRatios.model_surface_open
#print axioms CycleQ2LiteralAmbientCubicRatios.surface_normalized
#print axioms CycleQ2LiteralAmbientCubicRatios.surface_cubic_transition
#print axioms CycleQ2LiteralAmbientCubicRatios.surface_scalarUnit
