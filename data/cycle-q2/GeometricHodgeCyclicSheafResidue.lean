import Proposal.GeometricHodgeCyclicCharts
import Proposal.GeometricHodgeCyclicResidue
import Proposal.GeometricHodgeEulerContractionSheaf
import Proposal.GeometricHodgeGradientAtlas
import Proposal.GeometricLiteralThreefoldOrbitHodgePullbackForms
import Proposal.GeometricExteriorPullComposition

/-!
# The residue character on the Kähler sheaf of the projective threefold

Every principal gradient open in a normalized coordinate chart is stable.
The induced map on its coordinate algebra is the localized diagonal
action. Pullback through the scheme differential therefore gives the
computed character on the local projective residue and on its contraction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicSheafResidue
open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
  CycleQ2HodgeCyclicAction CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
  CycleQ2HodgeEulerContractionRestriction CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerTangentAtlas
  CycleQ2GeometricHodgeThreefold CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
  CycleQ2ChartSectionPullback CycleQ2ChartExteriorBinding CycleQ2GeometricDifferentialSheaf
  CycleQ2LiteralThreefoldOrbitHodgePullback CycleQ2ExteriorPullComposition
open CycleQ2GenericSexticGradient (CoeffRing)
open scoped KaehlerDifferential

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (i j : Fin 4)

abbrev grad := gradientEntry (F φ i) j
abbrev U := CycleQ2HodgeGradientAtlas.U φ i j
abbrev atlas := CycleQ2HodgeGradientAtlas.atlas φ i j
abbrev base := toBase φ

theorem overBase : (atlas φ i j).inv ≫ (U φ i j).ι ≫ base φ =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (gradientPatch φ i j))) :=
  CycleQ2HodgeGradientAtlas.atlas_overBase φ i j

theorem stable : (action φ z hz).hom ⁻¹ᵁ U φ i j = U φ i j := by
  let f := affineInclusion φ i
  let g := (action φ z hz).hom
  have hr : f.opensRange = coordinateOpen φ i :=
    (Scheme.Hom.opensRange_comp_of_isIso (affineChart φ i).inv (coordinateOpen φ i).ι).trans
      (Scheme.Opens.opensRange_ι _)
  have hle : g ⁻¹ᵁ U φ i j ≤ f.opensRange := by
    rw [hr, ← coordinateOpen_stable φ z hz i]
    exact g.preimage_mono ((f.image_le_opensRange _).trans hr.le)
  have hc : f ⁻¹ᵁ g ⁻¹ᵁ U φ i j = PrimeSpectrum.basicOpen (grad φ i j) := by
    rw [← Scheme.Hom.comp_preimage, affineInclusion_equivariant, Scheme.Hom.comp_preimage,
      U, CycleQ2HodgeGradientAtlas.U, Scheme.Hom.preimage_image_eq]
    change PrimeSpectrum.basicOpen (chartAction φ z hz i (gradientEntry (F φ i) j)) = _
    rw [chartAction_gradient, PrimeSpectrum.basicOpen_mul]
    have hu : IsUnit (algebraMap ℂ (chart φ i) (chartFactor z i j)⁻¹) :=
      (isUnit_iff_ne_zero.mpr (inv_ne_zero (chartFactor_ne_zero z hz i j))).map _
    have htop : PrimeSpectrum.basicOpen (algebraMap ℂ (chart φ i) (chartFactor z i j)⁻¹) = ⊤ :=
      top_unique fun p _ => Ideal.notMem_of_isUnit p.asIdeal hu
    rw [htop, top_inf_eq]
  change g ⁻¹ᵁ U φ i j = f ''ᵁ _
  rw [← hc, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hle]

theorem chart_square : (atlas φ i j).inv ≫ (U φ i j).ι ≫ (action φ z hz).hom =
    Spec.map (CommRingCat.ofHom (patchAction φ z hz i j).toRingHom) ≫
      (atlas φ i j).inv ≫ (U φ i j).ι := by
  rw [← Category.assoc, basicChart_inv_ι, basicChart_inv_ι, Category.assoc, affineInclusion_equivariant,
    ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun p => Spec.map p ≫ affineInclusion φ i)
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun a => (patchAction_base φ z hz i j a).symm)

abbrev chartForm (n : ℕ) := chartExteriorSheafSection (atlas φ i j) (base φ) (overBase φ i j) n (chartTop _)
abbrev κ := schemeCoefficient (toBase φ)
abbrev pulling (n : ℕ) := formsMap (action φ z hz).hom (κ φ) (κ φ)
    (compatible_over _ _ _ (action_overBase φ z hz)) n

theorem section_pull (n : ℕ) (ω : ⋀[gradientPatch φ i j]^n Ω[gradientPatch φ i j⁄ℂ]) :
    (forms (threefold φ) (κ φ) n).val.map (homOfLE (stable φ z hz i j).ge).op
      ((pulling φ z hz n).val.app (op (U φ i j)) (chartForm φ i j n ω)) =
      chartForm φ i j n (pull (patchAction φ z hz i j) n ω) := by
  apply formsMap_sectionLift_restrict (action φ z hz).hom (κ φ) (κ φ)
    (compatible_over _ _ _ (action_overBase φ z hz)) n (U φ i j)
    (chartSection (atlas φ i j) (chartTop _)) (chartSection_complex _ _ (overBase φ i j) _)
    (U φ i j) (stable φ z hz i j).ge (chartSection (atlas φ i j) (chartTop _))
    (chartSection_complex _ _ (overBase φ i j) _) (patchAction φ z hz i j) _ ω
  exact chartSection_pullback_top _ _ _ _ (stable φ z hz i j).ge (chart_square φ z hz i j)

theorem residue :
    (forms (threefold φ) (κ φ) 3).val.map (homOfLE (stable φ z hz i j).ge).op
      ((pulling φ z hz 3).val.app (op (U φ i j)) (chartForm φ i j 3 (projectiveResidue (F φ i) i j))) =
      CycleQ2GeometricDifferentialSheaf.coefficientOn (threefold φ).sheaf (κ φ) (U φ i j) (z^2) •
        chartForm φ i j 3 (projectiveResidue (F φ i) i j) := by
  rw [section_pull, patchAction_residue, map_smulₛₗ, chartSection_complex _ _ (overBase φ i j)]

theorem contraction_fixed (v : Derivation ℂ (gradientPatch φ i j) (gradientPatch φ i j))
    (hv : conjugate (patchEquiv φ z hz i j) v = algebraMap ℂ (gradientPatch φ i j) z • v) :
    (forms (threefold φ) (κ φ) 2).val.map (homOfLE (stable φ z hz i j).ge).op
      ((pulling φ z hz 2).val.app (op (U φ i j)) (chartForm φ i j 2 (familyContraction φ i j v))) =
      chartForm φ i j 2 (familyContraction φ i j v) := by
  rw [section_pull, character_one_contraction_fixed φ z hz i j v hv]

end CycleQ2HodgeCyclicSheafResidue
end
#print axioms CycleQ2HodgeCyclicSheafResidue.residue
#print axioms CycleQ2HodgeCyclicSheafResidue.contraction_fixed
