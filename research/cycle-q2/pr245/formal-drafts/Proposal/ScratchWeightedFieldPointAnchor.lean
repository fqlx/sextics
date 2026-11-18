import Proposal.ScratchWeightedGenericPointMap
import Proposal.ScratchCechKPointSections

/-! The actual K-point of the weighted threefold obtained from the evaluation
of its chosen native affine chart into the universal function field. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry CycleQ2.Cech
open CycleQ2WeightedResidueAtlas CycleQ2WeightedIntersectionFrame CycleQ2GeometricHodgeThreefold
open CycleQ2WeightedConeUniversal CycleQ2WeightedGenericPointMap
open scoped CycleQ2WeightedConeUniversal

namespace CycleQ2WeightedFieldPointAnchor
abbrev T := threefold coefficients
abbrev V := U coefficients chosen
local instance : Algebra Base Γ(T,V) := Sections.algebra (toBase coefficients) V

def g : Spec (CommRingCat.of FunctionField) ⟶ T :=
  Spec.map (CommRingCat.ofHom genericPoint.toRingHom) ≫ (affine coefficients chosen).fromSpec

theorem overBase : g ≫ toBase coefficients =
    Spec.map (CommRingCat.ofHom (algebraMap Base FunctionField)) := by
  rw [g,Category.assoc,← baseMap_spec _ (affine coefficients chosen),← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact genericPoint.comp_algebraMap

theorem preimage : g ⁻¹ᵁ V = ⊤ := by
  rw [g,Scheme.Hom.comp_preimage,IsAffineOpen.fromSpec_preimage_self,Scheme.Hom.preimage_top]

theorem anchor : KPoint.point g ∈ V := by
  let x : PrimeSpectrum FunctionField := ⊥
  change x ∈ g ⁻¹ᵁ V
  rw [preimage]
  trivial

/-- The support complement contains the chosen point as soon as a local
defining equation evaluates nontrivially in the literal field. -/
theorem point_mem_basicOpen (t : Γ(T,V)) :
    KPoint.point g ∈ T.basicOpen t ↔ genericPoint t ≠ 0 := by
  change (⊥ : PrimeSpectrum FunctionField) ∈ g ⁻¹ᵁ T.basicOpen t ↔ _
  rw [g,Scheme.Hom.comp_preimage,(affine coefficients chosen).fromSpec_preimage_basicOpen]
  change genericPoint t ∉ (⊥ : Ideal FunctionField) ↔ _
  simp

theorem point_mem_of_basicOpen {W : T.Opens} (t : Γ(T,V))
    (ht : genericPoint t ≠ 0) (hw : T.basicOpen t ≤ W) : KPoint.point g ∈ W :=
  hw ((point_mem_basicOpen t).mpr ht)

theorem evaluation : KPoint.evalRing g V anchor = genericPoint.toRingHom := by
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  apply (cancel_mono (affine coefficients chosen).fromSpec).mp
  change Spec.map (g.appLE V ⊤ _ ≫ (Scheme.ΓSpecIso (CommRingCat.of FunctionField)).hom) ≫
    (affine coefficients chosen).fromSpec = g
  rw [Spec.map_comp,Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec g
    (affine coefficients chosen) (isAffineOpen_top _) _,SpecMap_ΓSpecIso_hom,
    IsAffineOpen.fromSpec_top,Scheme.toSpecΓ_isoSpec_inv_assoc]

theorem evaluation_algHom : KPoint.eval (toBase coefficients) g overBase V anchor = genericPoint :=
  AlgHom.ext (fun a => RingHom.congr_fun evaluation a)

end CycleQ2WeightedFieldPointAnchor
end
#print axioms CycleQ2WeightedFieldPointAnchor.g
#print axioms CycleQ2WeightedFieldPointAnchor.evaluation_algHom
