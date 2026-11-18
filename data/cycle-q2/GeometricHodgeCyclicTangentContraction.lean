import Proposal.GeometricHodgeCyclicTangentFrames
import Proposal.GeometricHodgeCyclicVolume
import Proposal.GeometricHodgeVolumeContraction

/-! # Compatibility of the native Euler tangent and exterior actions

Every differential on a subopen of a gradient patch expands in the three
normalized projective-coordinate differentials. Covariance on these
coordinates determines evaluation on every one-form. Naturality of
interior multiplication then compares pullback on the second exterior
sheaf with the action on the projective normal kernel.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicTangentContraction
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
  CycleQ2HodgeCyclicTangentFrames CycleQ2HodgeCyclicTwistFrames CycleQ2HodgeCyclicTwistMaps
  CycleQ2HodgeCyclicNormalSequence CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf
  CycleQ2HodgeEulerTangentToQuotient CycleQ2HodgeEulerTangentSheaf CycleQ2HodgeEulerTangentValues
  CycleQ2HodgeEulerTangentCoordinates CycleQ2HodgeCyclicAction CycleQ2HodgeEuler
  CycleQ2HodgeEulerChartBinding CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerContractionSheaf
  CycleQ2HodgeVolumeContraction CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap
  CycleQ2GeometricAffineChartSections CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricPrincipalChartSections CycleQ2LiteralThreefoldDifferentialFrame
  CycleQ2GeometricExteriorSheaf CycleQ2LiteralThreefoldResidueContraction
  CycleQ2LiteralAbelJacobiQPullback CycleQ2ExteriorPullComposition
  CycleQ2GeometricTwistedDifferential CycleQ2HodgeEulerVolumeChart CycleQ2ChartExteriorBinding
  CycleQ2ExteriorSectionNaturality
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeGradientAtlas (U atlas U_le atlas_overBase atlas_inv_ι)

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (hg : IsUnit (φ goodParameter))
private abbrev O := threefold φ
private abbrev N := cotangent (toBase φ)
private abbrev c := schemeCoefficient (toBase φ)
private abbrev G := (action φ z hz).hom
private abbrev D := universalDifferential (O φ).sheaf (c φ)
private abbrev L := schemeDifferentialMap (G φ z hz) (c φ) (c φ)
    (compatible_over _ _ _ (action_overBase φ z hz))
abbrev toForms := toTangent φ hg ≫ (volumeIso φ hg).hom

variable (i j : Fin 4) (V : (O φ).Opens) (hi : V ≤ U φ i j)
private abbrev basisV := sectionBasis (atlas φ i j) (toBase φ) (atlas_overBase φ i j)
  (basis (F φ i) j) (Over.mk (homOfLE hi))

private theorem basis_coordinate (k : Fin 3) :
    basisV φ i j V hi k = (D φ).d (X := op V)
      (coordinateSection φ i V (hi.trans (U_le φ i j)) (i.castSucc.succAbove (j.succAbove k))) := by
  rw [basisV, sectionBasis_apply, basis_apply]
  change sectionLift _ _ _ _ V _ _ (KaehlerDifferential.D ℂ _ _) = _
  rw [sectionLift_D]
  apply congrArg ((D φ).d (X := op V))
  have h := chartSection_compatible (affineChart φ i) (atlas φ i j) (U_le φ i j)
    (patchMap (F φ i) j).toRingHom (atlas_inv_ι φ i j) (Over.mk (homOfLE hi))
    (chartMap φ i (X (j.succAbove k)))
  refine h.trans ?_
  have h' := chartSection_coordinate φ i V (hi.trans (U_le φ i j)) (i.castSucc.succAbove (j.succAbove k))
  simpa only [coordinate, dehom_X_succAbove] using h'

theorem evaluation_pull (v : Γ(rawTangent φ,V)) (x : Γ(N φ,V)) :
    let W := pre φ z hz V
    let u := (toTangent φ hg).app W ((actKernel φ z hz hg).app V v)
    evaluate (toBase φ) u (onSections (G φ z hz) (L φ z hz) V x) =
      (G φ z hz).app V (evaluate (toBase φ) ((toTangent φ hg).app V v) x) := by
  dsimp only
  let B := basisV φ i j V hi
  let A := onSections (G φ z hz) (L φ z hz) V
  let W := pre φ z hz V
  let u := (toTangent φ hg).app W ((actKernel φ z hz hg).app V v)
  let s := (toTangent φ hg).app V v
  change evaluate (toBase φ) u (A x) = (G φ z hz).app V (evaluate (toBase φ) s x)
  have hB (k : Fin 3) : evaluate (toBase φ) u (A (B k)) =
      (G φ z hz).app V (evaluate (toBase φ) s (B k)) := by
    rw [show B k = _ from basis_coordinate φ i j V hi k]
    change evaluate (toBase φ) u ((L φ z hz).val.app (op V) ((D φ).d _)) = _
    rw [L, schemeDifferentialMap_D]
    exact coordinate_derivation φ z hz hg i V (hi.trans (U_le φ i j)) v (j.succAbove k)
  rw [← B.sum_repr x]
  simp only [map_sum, map_smulₛₗ, map_smul, smul_eq_mul, map_mul, hB]

private theorem raw_natural (v : Γ(rawTangent φ,V))
    (ω : ⋀[Γ(O φ,V)]^3 Γ(N φ,V)) :
    let W := pre φ z hz V
    let s := (toTangent φ hg).app V v
    let t := (toTangent φ hg).app W ((actKernel φ z hz hg).app V v)
    (exteriorPull (G φ z hz) (L φ z hz) 2).val.app (op V)
      (contractSection (N φ) V s (exteriorSection (O φ).sheaf (N φ).val 3 V ω)) =
      contractSection (N φ) W t ((exteriorPull (G φ z hz) (L φ z hz) 3).val.app (op V)
        (exteriorSection (O φ).sheaf (N φ).val 3 V ω)) := by
  dsimp only
  rw [contractSection_exterior, exteriorPull_section, exteriorPull_section, contractSection_exterior]
  apply congrArg
  symm
  apply interior_natural
  exact evaluation_pull φ z hz hg i j V hi v

private abbrev ω (V : (O φ).Opens) :=
  (form (N φ) 3).val.map (homOfLE (le_top : V ≤ ⊤)).op (CycleQ2HodgeEulerVolume.omega φ hg)

private theorem volume_raw : ∃ x : ⋀[Γ(O φ,V)]^3 Γ(N φ,V), exteriorSection (O φ).sheaf (N φ).val 3 V x =
    ω φ hg V := by
  let P := U φ i j
  let V' : Over P := Over.mk (homOfLE hi)
  let k : V' ⟶ chartTop P := Over.homMk V'.hom
  let e := atlas φ i j
  let h := atlas_overBase φ i j
  let b := basis (F φ i) j
  let u := volumeUnit φ i j
  refine ⟨rawVolume e (toBase φ) h b u V', ?_⟩
  rw [← chartVolume_raw e (toBase φ) h b u V']
  have hw := CycleQ2HodgeEulerVolume.omega_on_gradient φ hg i j (U_le φ i j) e h (atlas_inv_ι φ i j)
  rw [projectiveResidue_eq_frame] at hw
  exact (chartExteriorSheafSection_restrict e (toBase φ) h k 3 _).symm.trans
    ((congrArg ((form (N φ) 3).val.map V'.hom.op) hw).symm.trans
      ((form (N φ) 3).val.map_comp_apply _ _ _).symm)

private theorem volume_action (V : (O φ).Opens) :
    (exteriorPull (G φ z hz) (L φ z hz) 3).val.app (op V) (ω φ hg V) =
      scalar φ (pre φ z hz V) (z^2) • ω φ hg (pre φ z hz V) := by
  let M := form (N φ) 3
  let T := exteriorPull (G φ z hz) (L φ z hz) 3
  let w := CycleQ2HodgeEulerVolume.omega φ hg
  let f := homOfLE (le_top : V ≤ ⊤)
  let f' := (Opens.map (G φ z hz).base).map f
  have hn := PresheafOfModules.naturality_apply T.val f.op w
  change T.val.app (op V) (M.val.map f.op w) = M.val.map f'.op (T.val.app (op ⊤) w) at hn
  rw [show T.val.app (op ⊤) w = scalar φ ⊤ (z^2) • w from
    CycleQ2HodgeCyclicVolume.omega_pull φ hg z hz, M.val.map_smul] at hn
  exact hn.trans (congrArg (fun r => r • M.val.map f'.op w)
    (coefficientOn_restrict (O φ).sheaf (c φ) f'.le (z^2)))

theorem local_equivariance (v : Γ(rawTangent φ,V)) :
    let W := pre φ z hz V
    (exteriorPull (G φ z hz) (L φ z hz) 2).val.app (op V) ((toForms φ hg).app V v) =
      scalar φ W (z^2) • (toForms φ hg).app W ((actKernel φ z hz hg).app V v) := by
  dsimp only
  let W := pre φ z hz V
  let s := (toTangent φ hg).app V v
  let t := (toTangent φ hg).app W ((actKernel φ z hz hg).app V v)
  change (exteriorPull (G φ z hz) (L φ z hz) 2).val.app (op V) ((volumeIso φ hg).hom.app V s) =
    scalar φ W (z^2) • (volumeIso φ hg).hom.app W t
  rw [volumeIso_apply, volumeIso_apply]
  obtain ⟨x,hx⟩ := volume_raw φ hg i j V hi
  change _ (contractSection (N φ) V s (ω φ hg V)) = scalar φ W (z^2) • contractSection (N φ) W t (ω φ hg W)
  rw [← hx, raw_natural φ z hz hg i j V hi v x, hx, volume_action, map_smul]

end CycleQ2HodgeCyclicTangentContraction
end

#print axioms CycleQ2HodgeCyclicTangentContraction.evaluation_pull
