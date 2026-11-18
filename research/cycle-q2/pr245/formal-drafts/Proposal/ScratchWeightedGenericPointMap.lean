import Proposal.ScratchWeightedIntersectionFrame
import Proposal.WeightedConeUniversalDeRham
import Proposal.GeometricHodgeEulerContractionRestriction

/-! The algebra homomorphism from the actual structure ring of the selected
gradient open to the function field of the universal monic threefold. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2.Cech.Sections CycleQ2WeightedResidueAtlas CycleQ2WeightedIntersectionFrame
  CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2GenericSexticGradient
  CycleQ2HodgeEulerChartDerivations CycleQ2HodgeEulerContractionCharts
open CycleQ2HodgeEulerContractionRestriction (fromPatch fromPatch_comp)
namespace CycleQ2WeightedGenericPointMap
variable {k : Type} [CommRing k] (φ : CoeffRing →+* k) (a : Index)

private def vertexIso : CommRingCat.of (Model φ a) ≅ Γ(threefold φ,U φ a) where
  hom := Spec.preimage ((affine φ a).isoSpec.inv ≫ (atlas φ a).hom)
  inv := Spec.preimage ((atlas φ a).inv ≫ (affine φ a).isoSpec.hom)
  hom_inv_id := by simp [← Spec.preimage_comp]
  inv_hom_id := by simp [← Spec.preimage_comp]

def coordinateEquiv :
    letI := algebra (toBase φ) (U φ a)
    Model φ a ≃ₐ[k] Γ(threefold φ,U φ a) := by
  letI := algebra (toBase φ) (U φ a)
  refine { (vertexIso φ a).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro t
  have h := RingHom.congr_fun (patch_overBase φ a (affine φ a) (le_refl _)) t
  symm
  simpa [patchMapToSection,vertexIso,Scheme.homOfLE_refl] using h

section Universal
open CycleQ2WeightedConeUniversal
open scoped CycleQ2WeightedConeUniversal
open CycleQ2GenericWeightedSpatialDenominator (universalAffine)
open CycleQ2MonicWeightedPrimitiveSpecialization (projection projection_kernel fieldValue)
abbrev chosen : Index := (0,0)

def ambientValue : Poly Base →ₐ[Base] FunctionField :=
  { value with commutes' := fun c => MvPolynomial.eval₂Hom_C _ _ _ }

theorem equation_zero : ambientValue affineEquation = 0 := by
  change value affineEquation = 0
  rw [affineEquation,chart_equation,value_map]
  change algebraMap _ _ (projection universalAffine universalAffine) = 0
  rw [(projection_kernel _ _).mpr (dvd_refl _),map_zero]

def hypersurfaceValue : Hyp affineEquation →ₐ[Base] FunctionField :=
  Ideal.Quotient.liftₐ _ ambientValue
    ((Ideal.span_singleton_le_iff_mem ambientValue.toRingHom.ker).mpr equation_zero)

theorem normal_nonzero : hypersurfaceValue (gradientEntry affineEquation 0) ≠ 0 := by
  change value (pderiv 0 (F coefficients 0)) ≠ 0
  have h := generic_normal
  change value (dehom 0 (pderiv 1 (equation coefficients))) ≠ 0 at h
  rwa [← show pderiv 0 (F coefficients 0) = dehom 0 (pderiv 1 (equation coefficients)) from
    pderiv_dehom (0 : Fin 4) (0 : Fin 4) (equation coefficients)] at h

def patchValue : Model coefficients chosen →ₐ[Base] FunctionField :=
  fromPatch affineEquation 0 hypersurfaceValue (isUnit_iff_ne_zero.mpr normal_nonzero)

def genericPoint :
    letI := algebra (toBase coefficients) (U coefficients chosen)
    Γ(threefold coefficients,U coefficients chosen) →ₐ[Base] FunctionField :=
  letI := algebra (toBase coefficients) (U coefficients chosen)
  patchValue.comp (coordinateEquiv coefficients chosen).symm.toAlgHom

theorem genericPoint_coordinate (p : Poly Base) :
    letI := algebra (toBase coefficients) (U coefficients chosen)
    genericPoint ((coordinateEquiv coefficients chosen)
      (patchMap affineEquation 0 (mk affineEquation p))) = value p := by
  letI := algebra (toBase coefficients) (U coefficients chosen)
  simp only [genericPoint, AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  change ((fromPatch affineEquation 0 hypersurfaceValue _).comp
    (patchMap affineEquation 0)) (mk _ p) = _
  rw [fromPatch_comp]
  rfl

end Universal
end CycleQ2WeightedGenericPointMap
end
#print axioms CycleQ2WeightedGenericPointMap.genericPoint_coordinate
