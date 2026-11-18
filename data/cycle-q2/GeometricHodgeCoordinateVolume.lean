import Proposal.GeometricHodgeEulerVolume
import Proposal.GeometricHodgeEulerTangentCoordinates

/-!
# The moving oriented residue multiplied by the first free partial

In the zeroth projective frame, the product of the global volume with the
normalized x₁ partial is the intrinsic wedge dx₂ ∧ dx₃ ∧ dw on every
subopen of the normalized coordinate chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCoordinateVolume

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeTwistRatios
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeEulerSheaf (partialValue partial_mem)
open CycleQ2HodgeEulerChartBinding (affineChart affineChart_overBase)
open CycleQ2HodgeEuler (chart F chartMap coordinate dehom_X_succAbove partial_succAbove)
open CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerVolumeChart
open CycleQ2HodgeEulerVolume (threeForms gradient_unit omega omega_restrict)
open CycleQ2LiteralThreefoldResidueMinors (signedOmitted signedOmitted_cross)
open CycleQ2GeometricAffineChartSections (chartSection schemeCoefficient)
open CycleQ2GeometricDifferentialSheaf (universalDifferential)
open CycleQ2GeometricSheafKaehlerMap (sectionLift_D)
open CycleQ2ChartExteriorBinding (chartExteriorSheafSection chartExteriorSheafSection_restrict)
open CycleQ2ExteriorSectionNaturality (exteriorSectionLift exteriorSectionLift_wedge)
open CycleQ2GeometricExteriorSheaf (exteriorSection)
open CycleQ2HodgeEulerTangentCoordinates (chartSection_coordinate chartSection_partial)
open CycleQ2HodgeEulerTangentSheaf (cotangent)
open scoped KaehlerDifferential

variable (φ : CoeffRing →+* ℂ) (hφ : IsUnit (φ goodParameter))

private abbrev coordinateSection (i : Fin 4) (W : (threefold φ).Opens) (hi : W ≤ U φ i) (j : Fin 5) :=
  normalized φ i (coord φ j) (coord_mem_grade φ j) W hi

abbrev A := chart φ 0
abbrev f := toBase φ
abbrev e := affineChart φ 0
private abbrev hg := gradient_unit φ hφ
abbrev coordIndex (k : Fin 3) := (0 : Fin 5).succAbove ((0 : Fin 4).succAbove k)

private theorem gradient_volume :
    gradientEntry (F φ 0) 0 • orientedVolume φ (hg φ hφ) 0 =
      exteriorPower.ιMulti (A φ) 3 (dx (F φ 0) (AlgHom.id ℂ (A φ)) ∘ (0 : Fin 4).succAbove) := by
  let z := signedOmitted (A φ) (dx (F φ 0) (AlgHom.id ℂ (A φ)))
  have h (j : Fin 4) :
      gradientEntry (F φ 0) 0 • z j = gradientEntry (F φ 0) j • z 0 :=
    signedOmitted_cross _ _ (gradient_relation (F φ 0) (AlgHom.id ℂ (A φ))) j 0
  change gradientEntry (F φ 0) 0 • ((-1 : A φ)^0 • ∑ j, coefficient φ (hg φ hφ) 0 j • z j) = _
  rw [pow_zero, one_smul, Finset.smul_sum]
  calc
    _ = ∑ j, (coefficient φ (hg φ hφ) 0 j * gradientEntry (F φ 0) j) • z 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_comm _ (coefficient φ (hg φ hφ) 0 j), h, mul_smul]
    _ = z 0 := by rw [← Finset.sum_smul, coefficient_identity, one_smul]
    _ = _ := by simp only [z, signedOmitted, Fin.val_zero, pow_zero, one_smul]

variable (W : (threefold φ).Opens) (h₀ : W ≤ U φ 0)
abbrev forms (k : Fin 3) : Γ(cotangent (f φ),W) :=
  (universalDifferential (threefold φ).sheaf (schemeCoefficient (f φ))).d (X := op W)
    (coordinateSection φ 0 W h₀ (coordIndex k))

abbrev restrictedOmega := (threeForms φ).val.map (homOfLE (le_top : W ≤ ⊤)).op (omega φ hφ)

private theorem gradient_value :
    chartSection (e φ) (Over.mk (homOfLE h₀)) (gradientEntry (F φ 0) 0) =
      normalized φ 0 (partialValue φ (1 : Fin 4).castSucc) (partial_mem φ _) W h₀ := by
  have he := chartSection_partial φ 0 W h₀ ((0 : Fin 5).succAbove (0 : Fin 4))
  rw [partial_succAbove] at he
  exact he

private theorem coord_value (k : Fin 3) :
    chartSection (e φ) (Over.mk (homOfLE h₀)) (chartMap φ 0 (X ((0 : Fin 4).succAbove k))) =
      coordinateSection φ 0 W h₀ (coordIndex k) := by
  have he := chartSection_coordinate φ 0 W h₀ ((0 : Fin 5).succAbove ((0 : Fin 4).succAbove k))
  rw [coordinate, dehom_X_succAbove] at he
  exact he

private theorem coordinate_wedge :
    chartExteriorSheafSection (e φ) (f φ) (affineChart_overBase φ 0) 3 (Over.mk (homOfLE h₀))
      (exteriorPower.ιMulti (A φ) 3 (dx (F φ 0) (AlgHom.id ℂ (A φ)) ∘ (0 : Fin 4).succAbove)) =
    exteriorSection (threefold φ).sheaf (cotangent (f φ)).val 3 W (exteriorPower.ιMulti _ 3 (forms φ W h₀)) := by
  change exteriorSectionLift _ _ _ _ W _ _ 3 (exteriorPower.ιMulti (A φ) 3 _) = _
  rw [exteriorSectionLift_wedge]
  change exteriorSection _ _ _ _ (exteriorPower.ιMulti _ 3 _) = _
  apply congrArg (exteriorSection _ _ _ W)
  apply congrArg (exteriorPower.ιMulti _ 3)
  funext k
  simp only [Function.comp_apply, dx, AlgHom.id_apply, sectionLift_D]
  exact congrArg ((universalDifferential (threefold φ).sheaf (schemeCoefficient (f φ))).d (X := op W))
    (coord_value φ W h₀ k)

theorem partial_volume :
    normalized φ 0 (partialValue φ (1 : Fin 4).castSucc) (partial_mem φ _) W h₀ •
      restrictedOmega φ hφ W = exteriorSection (threefold φ).sheaf (cotangent (f φ)).val 3 W
        (exteriorPower.ιMulti _ 3 (forms φ W h₀)) := by
  let E := chartExteriorSheafSection (e φ) (f φ) (affineChart_overBase φ 0) 3 (Over.mk (homOfLE h₀))
  have hΩ : restrictedOmega φ hφ W = E (orientedVolume φ (hg φ hφ) 0) :=
    CycleQ2HodgeEulerVolume.omega_restrict_subopen φ hφ 0 h₀
  have he := congrArg E (gradient_volume φ hφ)
  rw [map_smulₛₗ, ← hΩ, gradient_value, coordinate_wedge] at he
  exact he

end CycleQ2HodgeCoordinateVolume
end
#print axioms CycleQ2HodgeCoordinateVolume.partial_volume
