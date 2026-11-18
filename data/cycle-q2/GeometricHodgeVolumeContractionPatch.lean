import Proposal.GeometricHodgeVolumeContractionDual
import Proposal.GeometricHodgeEulerContraction

/-!
# Contraction with a generating volume on a free cotangent chart

Every subopen inherits the three differential basis sections. Their
unit-scaled determinant identifies the ordinary dual with the second
exterior power. These isomorphisms commute with restriction and hence
induce an isomorphism of the genuine sheaves on the original chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeVolumeContraction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricDifferentialRestriction CycleQ2GeometricAffineChartSections
  CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricFunctionalDifferentials
  CycleQ2LiteralThreefoldDifferentialFrame CycleQ2HodgeEulerContractionSheaf
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricExteriorLocalFrames CycleQ2HodgeEulerContraction
  CycleQ2LiteralThreefoldResidueContraction CycleQ2LocalSheafificationFrame
  CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A)) (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  (b : Basis (Fin 3) A (KaehlerDifferential ℂ A)) (u : Aˣ)

def rawVolume (V : Over U) : ⋀[Γ(X,V.left)]^3 ((oneForms f).val.obj (op V.left)) :=
  chartSection e V (u : A) • exteriorPower.ιMulti _ 3 (sectionBasis e f h b V)

theorem rawVolume_restrict {V W : Over U} (a : V ⟶ W) :
    exteriorMap (X.presheaf.map a.left.op).hom ((oneForms f).val.restrictₛₗ a.left.op) 3
      (rawVolume e f h b u W) = rawVolume e f h b u V := by
  rw [rawVolume, map_smulₛₗ, exteriorMap_wedge, chartSection_naturality e a]
  apply congrArg (_ • ·)
  apply congrArg (exteriorPower.ιMulti _ 3)
  funext j
  exact basis_restrict e f h b a j

theorem chartVolume_raw (V : Over U) :
    chartExteriorSheafSection e f h 3 V ((u : A) • exteriorPower.ιMulti A 3 b) =
      exteriorSection X.sheaf (oneForms f).val 3 V.left (rawVolume e f h b u V) := by
  rw [map_smulₛₗ, rawVolume, map_smul]
  apply congrArg (_ • ·)
  change exteriorSectionLift _ _ _ _ _ _ _ 3 (exteriorPower.ιMulti A 3 b) = _
  rw [exteriorSectionLift_wedge]
  change exteriorSection X.sheaf (oneForms f).val 3 V.left (exteriorPower.ιMulti _ 3 _) = _
  apply congrArg (exteriorSection X.sheaf (oneForms f).val 3 V.left)
  apply congrArg (exteriorPower.ιMulti _ 3)
  funext j
  exact (sectionBasis_apply e f h b V j).symm

def rawEquiv (V : Over U) :
    (dual (oneForms f)).val.obj (op V.left) ≃ₗ[Γ(X,V.left)]
      (⋀[Γ(X,V.left)]^2 ((oneForms f).val.obj (op V.left))) :=
  (evaluationEquiv e f h b V).trans
    (unitContractionEquiv (sectionBasis e f h b V) (Units.map (chartSection e V).toMonoidHom u))

theorem rawEquiv_apply (V : Over U) (v : (dual (oneForms f)).val.obj (op V.left)) :
    rawEquiv e f h b u V v = interior 2 (evaluation (oneForms f) V.left v) (rawVolume e f h b u V) :=
  unitContractionEquiv_apply _ _ _

private theorem rawEquiv_natural {V W : Over U} (a : V ⟶ W)
    (v : (dual (oneForms f)).val.obj (op W.left)) :
    exteriorMap (X.presheaf.map a.left.op).hom ((oneForms f).val.restrictₛₗ a.left.op) 2
      (rawEquiv e f h b u W v) =
      rawEquiv e f h b u V ((dual (oneForms f)).val.map a.left.op v) := by
  rw [rawEquiv_apply, rawEquiv_apply, ← rawVolume_restrict e f h b u a]
  symm
  apply interior_natural
  intro x
  exact localLinearHomEvaluate_restrict X.sheaf (oneForms f) _ a.left v x

private def rawIso : ((dual (oneForms f)).over U).val ≅
    overPresheaf (ringSheaf X.sheaf) (exteriorPresheaf X.sheaf.obj (oneForms f).val 2) U :=
  PresheafOfModules.isoMk (fun V => (rawEquiv e f h b u V.unop).toModuleIso) (by
    intro V W a
    apply ConcreteCategory.hom_ext
    intro v
    exact (rawEquiv_natural e f h b u a.unop v).symm)

def patchIso : (dual (oneForms f)).over U ≅ (form (oneForms f) 2).over U :=
  (@overIsoOfPresentation (show TopCat from X) (ringSheaf X.sheaf)
    (exteriorPresheaf X.sheaf.obj (oneForms f).val 2) U (form (oneForms f) 2)
    (toExteriorSheaf X.sheaf (oneForms f).val 2)
    (exteriorPresentation_locallyInjective X.sheaf (oneForms f).val 2)
    (exteriorPresentation_locallySurjective X.sheaf (oneForms f).val 2)
    ((dual (oneForms f)).over U) (rawIso e f h b u).symm).symm

theorem patchIso_apply (V : Over U) (δ : (dual (oneForms f)).val.obj (op V.left)) :
    (patchIso e f h b u).hom.val.app (op V) δ =
      contractSection (oneForms f) V.left δ
        (chartExteriorSheafSection e f h 3 V ((u : A) • exteriorPower.ιMulti A 3 b)) := by
  rw [chartVolume_raw, contractSection_exterior]
  change exteriorSection X.sheaf (oneForms f).val 2 V.left (rawEquiv e f h b u V δ) = _
  rw [rawEquiv_apply] <;> rfl

theorem patchIso_apply_of_volume (ω : (form (oneForms f) 3).val.obj (op ⊤))
    (hω : (form (oneForms f) 3).val.map (homOfLE (le_top : U ≤ ⊤)).op ω =
      chartExteriorSheafSection e f h 3 (chartTop U) ((u : A) • exteriorPower.ιMulti A 3 b))
    (V : Over U) (δ : (dual (oneForms f)).val.obj (op V.left)) :
    (patchIso e f h b u).hom.val.app (op V) δ =
      contractSection (oneForms f) V.left δ
        ((form (oneForms f) 3).val.map (homOfLE (le_top : V.left ≤ ⊤)).op ω) := by
  rw [patchIso_apply]
  apply congrArg
  let k : V ⟶ chartTop U := Over.homMk V.hom
  exact (chartExteriorSheafSection_restrict e f h k 3 _).symm.trans
    ((congrArg ((form (oneForms f) 3).val.map V.hom.op) hω).symm.trans
      ((form (oneForms f) 3).val.map_comp_apply _ _ ω).symm)

end CycleQ2HodgeVolumeContraction
end

#print axioms CycleQ2HodgeVolumeContraction.patchIso_apply
