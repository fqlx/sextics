import Proposal.GeometricHodgeCyclicTangentContraction
import Proposal.GeometricHodgeCyclicRepresentation
import Proposal.GeometricHodgeFixedCharacter
import Proposal.GeometricHodgeCyclicJacobian
import Proposal.GeometricHodgeTangentDeformations

/-! # Characters in the genuine upper Hodge group of the moving threefold

The comparison is the original projective connecting map, followed by
the radial quotient, the intrinsic tangent identification and contraction
with the global projective residue. Under native pullback the character
of a polynomial direction is shifted by the volume character.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicHodgePieces

open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite AlgebraicGeometry
  CycleQ2HodgeCyclicTangentContraction CycleQ2HodgeCyclicJacobian CycleQ2HodgeCyclicCohomology
  CycleQ2HodgeCyclicAction CycleQ2HodgeNormalCohomology CycleQ2GeometricHodgeThreefold
  CycleQ2HodgeEulerSheaf CycleQ2GeometricSheafCohomologyScalar CycleQ2ExteriorPullComposition
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteCechOrbitPullback
  CycleQ2HodgeJacobianDecomposition CycleQ2HodgeVolumeContraction
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2CechTwoToDerived (app app_res)
open CycleQ2HodgeGradientAtlas (U)
open CycleQ2HiggsJacobianFrames (gradedPiece)
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))
private abbrev X := threefold φ
private abbrev F := SheafOfModules.toSheaf (X φ).ringCatSheaf
private abbrev M := forms (X φ) (coeff φ) 2
private abbrev H := hodgeOne φ
private abbrev rawH := CycleQ2HodgeNormalCohomology.H φ (rawTangent φ) 1
private abbrev addMapForms := (F φ).map (toForms φ hg)
private abbrev addScalar (z : ℂ) := scalarEnd (X φ).sheaf (coeff φ) (M φ) z
local instance : Module ℂ (H φ) := cohomologyModule (X φ).sheaf (coeff φ) (M φ) 1 ⊤
local instance : Module ℂ (rawH φ) := cohomologyModule (X φ).sheaf (coeff φ) (rawTangent φ) 1 ⊤

variable (z : ℂ) (hz : z^3=1)
private abbrev g := (action φ z hz).hom
private abbrev P := additivePull (g φ z hz) (coeff φ) (coeff φ)
  (compatible_over _ _ _ (action_overBase φ z hz)) 2
private abbrev pRaw := (addMap φ z hz hg).τ₁
private abbrev qForms := addMapForms φ hg ≫ addScalar φ (z^2)

private theorem square : addMapForms φ hg ≫ P φ z hz =
    pRaw φ hg z hz ≫ (TopCat.Sheaf.pushforward AddCommGrpCat (g φ z hz).base).map (qForms φ hg z) := by
  let f := addMapForms φ hg ≫ P φ z hz
  let k := pRaw φ hg z hz ≫ (TopCat.Sheaf.pushforward AddCommGrpCat (g φ z hz).base).map (qForms φ hg z)
  let B := push (g φ z hz).base (hodgeSheaf φ)
  ext V v
  let W := V.unop
  change app f W v = app k W v
  apply B.eq_of_locally_eq' (fun a : Fin 4 × Fin 4 => W ⊓ U φ a.1 a.2) W
    (fun _ => homOfLE inf_le_left) (by rw [← inf_iSup_eq, CycleQ2HodgeGradientAtlas.cover φ hg]; exact le_inf le_rfl le_top)
  rintro ⟨i,j⟩
  let V' := W ⊓ U φ i j
  let h : V' ≤ W := inf_le_left
  change res B h (app f W v) = res B h (app k W v)
  rw [← app_res, ← app_res]
  exact local_equivariance φ z hz hg i j V' inf_le_right _

def rawToHodge := cohomologyMapLinear (X φ).sheaf (coeff φ) (rawTangent φ) (toForms φ hg) 1 ⊤

theorem rawToHodge_equivariant (v : rawH φ) :
    hodgeAction φ z hz (rawToHodge φ hg v) = z^2 • rawToHodge φ hg (rawAction φ z hz hg v) := by
  letI := toBase_proper φ
  letI : CompactSpace (X φ) := (quasiCompact_iff_compactSpace (toBase φ)).mp inferInstance
  have hs := CycleQ2HodgeCyclicConnecting.naturality (g φ z hz).base (addMapForms φ hg) (qForms φ hg z)
    (pRaw φ hg z hz) (P φ z hz) (square φ hg z hz) v
  change _ = (rawAction φ z hz hg v).comp (Ext.mk₀ (addMapForms φ hg ≫ addScalar φ (z^2))) _ at hs
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero] at hs
  exact hs

/-- The actual Hodge comparison through the original normal and radial exact sequences. -/
def equivalence : ((χ : ZMod 3) → gradedPiece φ 6 χ) ≃ₗ[ℂ] H φ :=
  (CycleQ2HodgeTangentDeformations.tangentDeformationEquiv φ hg).trans
    (cohomologyIsoLinear (X φ).sheaf (coeff φ) _ (volumeIso φ hg) 1 ⊤)

theorem equivalence_apply (a : (χ : ZMod 3) → gradedPiece φ 6 χ) :
    equivalence φ hg a = rawToHodge φ hg (normalDeformationEquiv φ hg a) := by
  let x := normalDeformationEquiv φ hg a
  let q := CategoryTheory.Limits.cokernel.π (radialTangent φ)
  let t := (CycleQ2HodgeEulerTangentDescent.quotientTangentIso φ hg).hom
  let c := (volumeIso φ hg).hom
  change ((x.comp (Ext.mk₀ ((F φ).map q)) _).comp (Ext.mk₀ ((F φ).map t)) _).comp (Ext.mk₀ ((F φ).map c)) _ =
    x.comp (Ext.mk₀ ((F φ).map ((q ≫ t) ≫ c))) _
  rw [Functor.map_comp, Functor.map_comp, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

theorem equivariant (a : (χ : ZMod 3) → gradedPiece φ 6 χ) :
    hodgeAction φ z hz (equivalence φ hg a) = equivalence φ hg (fun χ => (z^2 * z^χ.val) • a χ) := by
  rw [equivalence_apply, rawToHodge_equivariant, CycleQ2HodgeCyclicJacobian.equivariant,
    ← equivalence_apply, ← map_smul]
  apply congrArg (equivalence φ hg)
  funext χ
  exact (mul_smul (z^2) (z^χ.val) (a χ)).symm

private abbrev T := CycleQ2HodgeEulerTangentSheaf.tangent (toBase φ)
private abbrev tangentH := CycleQ2HodgeNormalCohomology.H φ (T φ) 1
local instance : Module ℂ (tangentH φ) := cohomologyModule (X φ).sheaf (coeff φ) (T φ) 1 ⊤

private abbrev contract := cohomologyIsoLinear (X φ).sheaf (coeff φ) _ (volumeIso φ hg) 1 ⊤

/-- Removing the volume character gives the ordinary tangent action. -/
def tangentAction : tangentH φ →ₗ[ℂ] tangentH φ :=
  (contract φ hg).symm.toLinearMap.comp (((z : ℂ) • CycleQ2HodgeCyclicRepresentation.linearAction φ z hz).comp
    (contract φ hg).toLinearMap)

theorem tangent_equivariant (a : (χ : ZMod 3) → gradedPiece φ 6 χ) :
    tangentAction φ hg z hz (CycleQ2HodgeTangentDeformations.tangentDeformationEquiv φ hg a) =
      CycleQ2HodgeTangentDeformations.tangentDeformationEquiv φ hg (fun χ => z^χ.val • a χ) := by
  apply (contract φ hg).injective
  change (contract φ hg) ((contract φ hg).symm (z • hodgeAction φ z hz (equivalence φ hg a))) =
    equivalence φ hg (fun χ => z^χ.val • a χ)
  rw [LinearEquiv.apply_symm_apply, equivariant, ← map_smul]
  apply congrArg (equivalence φ hg)
  funext χ
  change z • ((z^2 * z^χ.val) • a χ) = z^χ.val • a χ
  rw [← mul_smul, ← mul_assoc, show z * z^2 = z^3 by ring, hz, one_mul]

def tangentRepresentation : Representation ℂ (rootsOfUnity 3 ℂ) (tangentH φ) where
  toFun r := tangentAction φ hg (r.val : ℂ) ((mem_rootsOfUnity' 3 r.val).mp r.property)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨a,rfl⟩ := (CycleQ2HodgeTangentDeformations.tangentDeformationEquiv φ hg).surjective x
    rw [tangent_equivariant]
    change CycleQ2HodgeTangentDeformations.tangentDeformationEquiv φ hg (fun χ => (1:ℂ)^χ.val • a χ) = _
    simp
  map_mul' r s := by
    apply LinearMap.ext
    intro x
    obtain ⟨a,rfl⟩ := (CycleQ2HodgeTangentDeformations.tangentDeformationEquiv φ hg).surjective x
    change tangentAction φ hg _ _ _ = tangentAction φ hg _ _ (tangentAction φ hg _ _ _)
    rw [tangent_equivariant, tangent_equivariant, tangent_equivariant]
    apply congrArg (CycleQ2HodgeTangentDeformations.tangentDeformationEquiv φ hg)
    funext χ
    change (((r.val : ℂ) * (s.val : ℂ))^χ.val) • a χ =
      (r.val : ℂ)^χ.val • ((s.val : ℂ)^χ.val • a χ)
    rw [mul_pow, mul_smul]

/-- The full invariant upper Hodge piece is the character-one degree-six Jacobian summand. -/
def invariantEquivalence : gradedPiece φ 6 1 ≃ₗ[ℂ]
    (CycleQ2HodgeCyclicRepresentation.representation φ).invariants :=
  CycleQ2HodgeFixedCharacter.equivalence (gradedPiece φ 6) (equivalence φ hg)
    (CycleQ2HodgeCyclicRepresentation.representation φ) (fun r a =>
      equivariant φ hg (r.val : ℂ) ((mem_rootsOfUnity' 3 r.val).mp r.property) a)

end CycleQ2HodgeCyclicHodgePieces
end

#print axioms CycleQ2HodgeCyclicHodgePieces.invariantEquivalence
