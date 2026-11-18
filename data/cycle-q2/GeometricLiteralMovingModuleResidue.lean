import Proposal.GeometricLiteralMovingResidueSmooth
import Proposal.GeometricLiteralMovingModuleCartier

/-!
# The module residue of the moving Cartier curve

On the framed affine basis every curve one-form lifts from the surface.
Wedging a lift with the differential of the equation and forming its
simple pole are linear in the lift. The resulting residue therefore gives
a morphism of modules directly to the cokernel of the regular inclusion.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

noncomputable section
namespace CycleQ2LiteralMovingModuleResidue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafCurveBinding CycleQ2GeometricIntrinsicNormal
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralMovingResidueFaces
  CycleQ2LiteralMovingResiduePole CycleQ2LiteralMovingResidueCurve
  CycleQ2LiteralMovingResidueBasis CycleQ2LiteralMovingResidueGluing
  CycleQ2GeometricSchemeDifferentialMap CycleQ2LiteralNativeChernCocycle
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open CycleQ2LiteralMovingResidueBoundary (lift)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2LiteralMovingResidueExact (residueQuotient regularInclusion)
open CycleQ2LiteralMovingResidueAdjunction (numeratorLinear numeratorLinear_apply)
open CycleQ2LiteralMovingResidueAdjunction.AffineFrame (curveCoefficient curveMap_constants)

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

private abbrev scale (M : Surface.Modules) (W : Surface.Opens) (a : Γ(Surface,W)) (s : Γ(M,W)) : Γ(M,W) :=
  a • s

abbrev curveModule := (Scheme.Modules.pushforward (curveToSurface t)).obj (curveDifferentials t)

private theorem lift_smul {W : Surface.Opens} (j : FrameData W) (a : Γ(Surface,W)) (β : OneForms W) :
    lift t ht j (a • β) = a • (lift t ht j β : Γ(PoleForms t,W)) := by
  apply pole_ext t ht j
  intro V
  change (poleOfNumerator t ht j (poleNumerator t j (a • β))).val.app (op V) _ =
    scale CanonicalForms V.left (Surface.presheaf.map V.hom.op a)
      ((poleOfNumerator t ht j (poleNumerator t j β)).val.app (op V) _)
  rw [poleOfNumerator_app_frame, poleOfNumerator_app_frame, one_smul, one_smul]
  exact (congrArg (CanonicalForms.val.map V.hom.op) ((numeratorLinear t j).map_smul a β)).trans
    (CanonicalForms.val.map_smul V.hom.op a (poleNumerator t j β))

private theorem scalar_of_framed {M N : Surface.Modules} (u : addSheaf M ⟶ addSheaf N)
    (hu : ∀ (W : FramedAffine) (a : Γ(Surface,W.carrier)) (s : Γ(M,W.carrier)),
      u.hom.app (op W.carrier) (a • s) = scale N W.carrier a (u.hom.app (op W.carrier) s))
    (W : Surface.Opens) (a : Γ(Surface,W)) (s : Γ(M,W)) :
    u.hom.app (op W) (a • s) = scale N W a (u.hom.app (op W) s) := by
  let A := {v : FramedAffine // v.carrier ≤ W}
  have hc : W ≤ ⨆ v : A, v.val.carrier := by
    intro x hx
    obtain ⟨_,⟨v,rfl⟩,hv,hvW⟩ := Opens.isBasis_iff_nbhd.mp isBasis_framedAffine hx
    exact Opens.mem_iSup.mpr ⟨⟨v,hvW⟩,hv⟩
  apply (addSheaf N).eq_of_locally_eq' (fun v : A => v.val.carrier) W (fun v => homOfLE v.property) hc
  intro v
  let i := (homOfLE v.property).op
  have nat (z : Γ(M,W)) : N.val.map i (u.hom.app (op W) z) =
      u.hom.app (op v.val.carrier) (M.val.map i z) :=
    (ConcreteCategory.congr_hom (u.hom.naturality i) z).symm
  change N.val.map i (u.hom.app (op W) (a • s)) = N.val.map i (scale N W a (u.hom.app (op W) s))
  refine (nat _).trans ?_
  refine (congrArg (u.hom.app (op v.val.carrier)) (M.val.map_smul i a s)).trans ?_
  refine (hu v.val (Surface.presheaf.map i a) (M.val.map i s)).trans ?_
  exact (congrArg (scale N v.val.carrier (Surface.presheaf.map i a)) (nat s).symm).trans
    (N.val.map_smul i a (u.hom.app (op W) s)).symm

section Cokernel

variable {Q : Surface.Modules} (π : PoleForms t ⟶ Q) (c : residueQuotient t ⟶ addSheaf Q)
    (hc : cokernel.π (regularInclusion t) ≫ c = (SheafOfModules.toSheaf Surface.ringCatSheaf).map π)

include hc in
private theorem on_pullback (W : FramedAffine) (β : OneForms W.carrier) :
    (curveResidue t ht ≫ c).hom.app (op W.carrier) ((pullbackForms t).hom.app (op W.carrier) β) =
      π.val.app (op W.carrier) (lift t ht W.frame β) := by
  have hp := congrArg (fun u : differentialAddSheaf ⟶ residueQuotient t => u.hom.app (op W.carrier) β)
    (pullbackForms_curveResidue t ht)
  change (curveResidue t ht).hom.app _ ((pullbackForms t).hom.app (op W.carrier) β) = _ at hp
  change c.hom.app _ ((curveResidue t ht).hom.app _ ((pullbackForms t).hom.app (op W.carrier) β)) = _
  rw [hp, surfaceResidue_basis, framedResidue_apply]
  exact congrArg (fun u : addSheaf (PoleForms t) ⟶ addSheaf Q =>
    u.hom.app (op W.carrier) (lift t ht W.frame β)) hc

include hc in
private theorem scalar_on_framed (W : FramedAffine) (a : Γ(Surface,W.carrier)) (s : Γ(curveModule t,W.carrier)) :
    (curveResidue t ht ≫ c).hom.app (op W.carrier) (a • s) =
      scale Q W.carrier a ((curveResidue t ht ≫ c).hom.app (op W.carrier) s) := by
  obtain ⟨β,hβ⟩ := pullbackForms_surjective t W s
  subst s
  let F := schemeDifferentialMap (curveToSurface t) (curveCoefficient t) globalCoefficient
    (fun _ c => curveMap_constants t c)
  have hf : scale (curveModule t) W.carrier a ((pullbackForms t).hom.app (op W.carrier) β) =
      (pullbackForms t).hom.app (op W.carrier) (scale DifferentialSheaf W.carrier a β) :=
    ((F.val.app (op W.carrier)).hom.map_smul a β).symm
  refine (congrArg ((curveResidue t ht ≫ c).hom.app (op W.carrier)) hf).trans ?_
  refine (on_pullback t ht π c hc W _).trans ?_
  refine (congrArg (π.val.app (op W.carrier)) (lift_smul t ht W.frame a β)).trans ?_
  refine ((π.val.app (op W.carrier)).hom.map_smul a _).trans ?_
  exact congrArg (scale Q W.carrier a) (on_pullback t ht π c hc W β).symm

end Cokernel

-- Module quotient specialization
open CycleQ2LiteralMovingModuleCartier (inclusion quotient quotientAddIso projection_quotientAddIso)

private theorem compare_projection :
    cokernel.π (regularInclusion t) ≫ (quotientAddIso t).inv =
      (SheafOfModules.toSheaf Surface.ringCatSheaf).map (cokernel.π (inclusion t)) := by
  rw [← projection_quotientAddIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The moving curve's Poincaré residue takes its values in the module cokernel. -/
def moduleResidue : curveModule t ⟶ quotient t where
  val := PresheafOfModules.homMk (curveResidue t ht ≫ (quotientAddIso t).inv).hom
    (fun U a s => scalar_of_framed (M := curveModule t) (N := quotient t) _
      (scalar_on_framed t ht _ _ (compare_projection t)) U.unop a s)

/-- A surface lift of the curve form gives the projected logarithmic pole
on each actual framed affine open. -/
theorem moduleResidue_on_pullback (W : FramedAffine) (β : OneForms W.carrier) :
    (moduleResidue t ht).val.app (op W.carrier) ((pullbackForms t).hom.app (op W.carrier) β) =
      (cokernel.π (inclusion t)).val.app (op W.carrier) (lift t ht W.frame β) :=
  on_pullback t ht (cokernel.π (inclusion t)) (quotientAddIso t).inv (compare_projection t) W β

/-- Forgetting module structure and identifying cokernels recovers the original residue. -/
theorem moduleResidue_additive :
    (SheafOfModules.toSheaf Surface.ringCatSheaf).map (moduleResidue t ht) ≫
      (quotientAddIso t).hom = curveResidue t ht := by
  change (curveResidue t ht ≫ (quotientAddIso t).inv) ≫ (quotientAddIso t).hom = _
  simp

/-- On the chosen independent moving member the module residue identifies
the direct image of curve differentials with the actual pole quotient. -/
theorem moduleResidue_isIso (hi : AlgebraicIndependent ℚ t) : IsIso (moduleResidue t ht) := by
  let := CycleQ2LiteralMovingResidueSmooth.curveResidue_isIso_of_independent t ht hi
  have : IsIso ((Scheme.Modules.toPresheaf Surface).map (moduleResidue t ht)) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map (curveResidue t ht ≫ (quotientAddIso t).inv)))
  exact isIso_of_reflects_iso (moduleResidue t ht) (Scheme.Modules.toPresheaf Surface)

end CycleQ2LiteralMovingModuleResidue
end

#print axioms CycleQ2LiteralMovingModuleResidue.moduleResidue_additive

#print axioms CycleQ2LiteralMovingModuleResidue.moduleResidue_isIso
