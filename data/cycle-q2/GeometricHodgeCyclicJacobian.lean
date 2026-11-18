import Proposal.GeometricHodgeCyclicNormalSequence
import Proposal.GeometricHodgeCyclicConnecting
import Proposal.GeometricHodgeJacobianDecomposition

/-! # The normal connecting class has the original polynomial character

The action comes from pullback of the normal exact sequence of the
original moving hypersurface. Its action on a polynomial deformation
can be evaluated on the four native projective frames and then descended
to each degree-six Jacobian summand.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicJacobian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  CycleQ2HodgeCyclicNormalSequence CycleQ2HodgeCyclicTwistMaps CycleQ2HodgeCyclicTwistFrames
  CycleQ2HodgeCyclicAction CycleQ2GeometricHodgeThreefold CycleQ2HodgeNormalCohomology
  CycleQ2HodgeEulerSheaf CycleQ2HodgeNormalDeformations CycleQ2HodgeThreefoldTwist
  CycleQ2HodgeInfinitesimalQuotient CycleQ2HodgeJacobianConnecting CycleQ2HodgeTwistRatios
  CycleQ2LiteralThreefoldOrbitAction CycleQ2GenericSexticGradient
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2SeedSectionSheafLocal (moduleRes)
open CycleQ2GeometricSheafCohomologyScalar (cohomologyModule)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
local instance (X : TopCat.{0}) : CategoryTheory.HasExt.{1} (AbSheaf X) :=
  CategoryTheory.HasExt.standard _

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (hg : IsUnit (φ goodParameter))
abbrev spaceAction := Scheme.forgetToTop.mapIso (action φ z hz)
private abbrev F := SheafOfModules.toSheaf (threefold φ).ringCatSheaf

def addMap : addNormal φ ⟶ (addNormal φ).map (CycleQ2AutomorphismGlobalSections.pushFunctor (spaceAction φ z hz)) where
  τ₁ := (F φ).map (actKernel φ z hz hg)
  τ₂ := (F φ).map (actRaw φ z hz hg)
  τ₃ := (F φ).map (actNormal φ z hz hg)
  comm₁₂ := by simpa only [Functor.map_comp] using congrArg (F φ).map (kernel_square φ z hz hg)
  comm₂₃ := by simpa only [Functor.map_comp] using congrArg (F φ).map (normal_square φ z hz hg)

def rawAction : H φ (rawTangent φ) 1 →+ H φ (rawTangent φ) 1 :=
  CycleQ2LiteralAbelJacobiQPullbackDerived.pullH (spaceAction φ z hz).hom (addMap φ z hz hg).τ₁ 1

theorem connecting_action (s : Γ(twist φ 6,⊤)) :
    rawAction φ z hz hg (connecting φ hg s) = connecting φ hg ((actNormal φ z hz hg).app ⊤ s) := by
  letI := toBase_proper φ
  letI : CompactSpace (threefold φ) := (quasiCompact_iff_compactSpace (toBase φ)).mp inferInstance
  exact CycleQ2HodgeCyclicConnecting.connecting (spaceAction φ z hz) (addNormal_exact φ hg)
    (addNormal_exact φ hg) (addMap φ z hz hg) s

local instance (V : (threefold φ).Opens) : Module ℂ Γ(twist φ 6,V) :=
  CycleQ2HodgeConnectingScalar.sectionModule (schemeCoefficient (toBase φ)) (twist φ 6) V
local instance : Module ℂ (H φ (rawTangent φ) 1) :=
  cohomologyModule (threefold φ).sheaf (schemeCoefficient (toBase φ)) (rawTangent φ) 1 ⊤

private theorem direction_local (χ : ZMod 3) (p : Directions ℂ χ) (i : Fin 4)
    (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    (actNormal φ z hz hg).app V (directionSection φ p V) = directionSection φ (z^χ.val • p) (pre φ z hz V) := by
  let W := pre φ z hz V
  let hi' := ((g φ z hz).preimage_mono hi).trans (coordinateOpen_stable φ z hz i).le
  apply (chartFrame φ 6 i W hi').injective
  rw [twistMap_frame φ z hz 6 1 hg i V hi]
  have d := direction_frame φ z hz i V W hi hi' le_rfl χ p
  rw [Scheme.Hom.appLE_eq_app] at d
  rw [d]
  have hs := (sectionLinear φ χ W).map_smul (z^χ.val) p
  change directionSection φ (z^χ.val • p) W = scalar φ W (z^χ.val) • directionSection φ p W at hs
  rw [hs, map_smul, smul_eq_mul]
  have h6 : char z i.castSucc ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3*2 by decide, pow_mul, char_cube z hz, one_pow]
  simp only [weight, one_mul, h6, map_one, one_mul]

theorem direction_action (χ : ZMod 3) (p : Directions ℂ χ) :
    (actNormal φ z hz hg).app ⊤ (directionSection φ p ⊤) = directionSection φ (z^χ.val • p) ⊤ := by
  apply TopCat.Presheaf.IsSheaf.section_ext ((push φ z hz).obj (twist φ 6)).isSheaf
  intro x hx
  have hxc : x ∈ (⨆ i, U φ i) := by rw [coordinateOpens_cover_of_good φ hg]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxc
  refine ⟨U φ i, le_top, hi, ?_⟩
  rw [← PresheafOfModules.naturality_apply]
  change (actNormal φ z hz hg).app _ (moduleRes _ _ (directionSection φ p ⊤)) =
    moduleRes (twist φ 6) _ (directionSection φ _ ⊤)
  simp only [directionSection, homogeneousSection_restrict]
  exact direction_local φ z hz hg χ p i _ le_rfl

theorem jacobian_action (χ : ZMod 3) (a : CycleQ2HiggsJacobianFrames.gradedPiece φ 6 χ) :
    rawAction φ z hz hg (jacobianClass φ χ hg a) = z^χ.val • jacobianClass φ χ hg a := by
  obtain ⟨p,rfl⟩ := directionClass_surjective φ χ a
  rw [jacobianClass_direction, connecting_action, direction_action]
  exact (polynomialClass φ χ hg).map_smul (z^χ.val) p

theorem equivariant (a : (χ : ZMod 3) → CycleQ2HiggsJacobianFrames.gradedPiece φ 6 χ) :
    rawAction φ z hz hg (CycleQ2HodgeJacobianDecomposition.normalDeformationEquiv φ hg a) =
      CycleQ2HodgeJacobianDecomposition.normalDeformationEquiv φ hg (fun χ => z^χ.val • a χ) := by
  change rawAction φ z hz hg (CycleQ2HodgeJacobianDecomposition.total φ hg a) =
    CycleQ2HodgeJacobianDecomposition.total φ hg _
  simp only [CycleQ2HodgeJacobianDecomposition.total, LinearMap.sum_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, map_sum, map_smul, jacobian_action]

end CycleQ2HodgeCyclicJacobian
end

#print axioms CycleQ2HodgeCyclicJacobian.equivariant
