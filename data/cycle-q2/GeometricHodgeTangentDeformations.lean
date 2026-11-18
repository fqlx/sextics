import Proposal.GeometricHodgeJacobianDecomposition
import Proposal.GeometricHodgeEulerTangentDescent

/-!
# First cohomology of the tangent sheaf of the moving threefold

On the four weight-one charts the radial quotient has actual local lifts.
The Euler sequence of additive sheaves is therefore short exact. Vanishing
of the first and second cohomology of O(0) identifies the first cohomology
of the normal kernel with that of the intrinsic tangent sheaf. Its polynomial
parameters are the three degree-six Jacobian summands.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTangentDeformations

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Abelian
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeNormalCohomology CycleQ2HodgeTwistRatios CycleQ2GeometricIncidenceProj
open CycleQ2GeometricSheafCohomologyScalar CycleQ2HodgeEulerTangentSheaf (tangent)
open CycleQ2GeometricOpenCoverAdditiveExactness (additiveComplex)
open CycleQ2InjectiveCech (freeOpen AbSheaf)
open CycleQ2GenericSexticGradient (CoeffRing)
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))
private abbrev coeff := CycleQ2GeometricAffineChartSections.schemeCoefficient (toBase φ)
local instance (M : (threefold φ).Modules) : Module ℂ (H φ M 1) :=
  cohomologyModule (threefold φ).sheaf (coeff φ) M 1 ⊤

abbrev addEuler := additiveComplex (eulerSequence φ)

theorem addEuler_exact_of_vertex (hv : IsUnit (φ vertexCoefficient)) : (addEuler φ).ShortExact := by
  let F := SheafOfModules.toSheaf (threefold φ).ringCatSheaf
  have hS := eulerSequence_exact φ
  have h := hS.exact.map_of_mono_of_preservesKernel F hS.mono_f inferInstance
  refine { exact := h, mono_f := ?_, epi_g := ?_ }
  · change Mono (F.map (radialTangent φ))
    infer_instance
  · change Epi (F.map (cokernel.π (radialTangent φ)))
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro V s x hx
    have hxc : x ∈ ⨆ i : Fin 4, U φ i := by rw [coordinateOpens_cover φ hv]; trivial
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxc
    refine ⟨V ⊓ U φ i, inf_le_left, ⟨CycleQ2HodgeEulerQuotientSections.representativeAt
      φ i _ inf_le_right _, ?_⟩, ⟨hx,hi⟩⟩
    exact CycleQ2HodgeEulerQuotientSections.representativeAt_project φ i _ inf_le_right _

def quotientMap : H φ (rawTangent φ) 1 →ₗ[ℂ] H φ (tangentQuotient φ) 1 :=
  cohomologyMapLinear (threefold φ).sheaf (coeff φ) _ (cokernel.π (radialTangent φ)) 1 ⊤

theorem quotientMap_bijective_of_vertex (hv : IsUnit (φ vertexCoefficient)) :
    Function.Bijective (quotientMap φ) := by
  have ht := CycleQ2HodgeTwistTorusChart.ordinary_vanishing φ hv 0
  let e (n : ℕ) := CycleQ2GeometricSheafCohomologyRestriction.terminalCohomologyEquiv
    (Opens.grothendieckTopology (threefold φ)) (Add φ (twist φ 0)) ⊤ isTerminalTop n
  haveI : Subsingleton (H φ (twist φ 0) 1) := by
    letI := ht.1
    exact (e 1).injective.subsingleton
  haveI : Subsingleton (H φ (twist φ 0) 2) := by
    letI := ht.2
    exact (e 2).injective.subsingleton
  let S := addEuler φ
  let A := freeOpen (⊤ : (threefold φ).Opens)
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₂ A (addEuler_exact_of_vertex φ hv) x hx
    have hz : a = 0 := Subsingleton.elim _ _
    rw [← ha, hz, Ext.zero_comp]
  · intro x
    have hz : x.comp (addEuler_exact_of_vertex φ hv).extClass (show 1+1=2 from rfl) = 0 := Subsingleton.elim _ _
    obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ A (addEuler_exact_of_vertex φ hv) x rfl hz
    exact ⟨a,ha⟩

theorem quotientMap_bijective : Function.Bijective (quotientMap φ) := by
  rw [goodParameter, map_mul, IsUnit.mul_iff] at hg
  exact quotientMap_bijective_of_vertex φ hg.2

def tangentDeformationEquiv :
    ((χ : ZMod 3) → CycleQ2HiggsJacobianFrames.gradedPiece φ 6 χ) ≃ₗ[ℂ] H φ (tangent (toBase φ)) 1 :=
  ((CycleQ2HodgeJacobianDecomposition.normalDeformationEquiv φ hg).trans
    (LinearEquiv.ofBijective (quotientMap φ) (quotientMap_bijective φ hg))).trans
    (cohomologyIsoLinear (threefold φ).sheaf (coeff φ) _
      (CycleQ2HodgeEulerTangentDescent.quotientTangentIso φ hg) 1 ⊤)

/-- The embedding of any character summand sends a polynomial to its actual projective
normal boundary, followed by the uniform Euler quotient into the relative tangent sheaf. -/
theorem tangentDeformationEquiv_direction (χ : ZMod 3)
    (p : CycleQ2HodgeInfinitesimalQuotient.Directions ℂ χ) :
    tangentDeformationEquiv φ hg (Pi.single χ (CycleQ2HodgeInfinitesimalQuotient.directionClass φ χ p)) =
      (connecting φ hg (CycleQ2HodgeNormalDeformations.directionSection φ p ⊤)).comp
        (Ext.mk₀ ((SheafOfModules.toSheaf (threefold φ).ringCatSheaf).map
          (cokernel.π (radialTangent φ) ≫ (CycleQ2HodgeEulerTangentDescent.quotientTangentIso φ hg).hom)))
        (Nat.add_zero 1) := by
  classical
  let a := CycleQ2HodgeInfinitesimalQuotient.directionClass φ χ p
  have h : CycleQ2HodgeJacobianDecomposition.normalDeformationEquiv φ hg (Pi.single χ a) =
      connecting φ hg (CycleQ2HodgeNormalDeformations.directionSection φ p ⊤) := by
    change (∑ ξ, (CycleQ2HodgeJacobianConnecting.jacobianClass φ ξ hg).comp (LinearMap.proj ξ))
      (Pi.single χ a) = _
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single χ]
    · rw [Pi.single_eq_same]
      exact CycleQ2HodgeJacobianConnecting.jacobianClass_direction φ χ hg p
    · intro ξ _ hξ
      rw [Pi.single_eq_of_ne hξ, map_zero]
    · simp
  let F := SheafOfModules.toSheaf (threefold φ).ringCatSheaf
  let π := cokernel.π (radialTangent φ)
  let ρ := (CycleQ2HodgeEulerTangentDescent.quotientTangentIso φ hg).hom
  change (((CycleQ2HodgeJacobianDecomposition.normalDeformationEquiv φ hg (Pi.single χ a)).comp
    (Ext.mk₀ (F.map π)) (add_zero 1)).comp (Ext.mk₀ (F.map ρ)) (add_zero 1)) =
    (connecting φ hg _).comp (Ext.mk₀ (F.map (π ≫ ρ))) (add_zero 1)
  rw [h, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Functor.map_comp]

end CycleQ2HodgeTangentDeformations
end

#print axioms CycleQ2HodgeTangentDeformations.tangentDeformationEquiv

#print axioms CycleQ2HodgeTangentDeformations.tangentDeformationEquiv_direction
