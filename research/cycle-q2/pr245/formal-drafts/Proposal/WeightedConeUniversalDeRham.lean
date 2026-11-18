import Proposal.WeightedConeDifferentialBasis
import Proposal.WeightedConeUniversalFrame
import Proposal.WeightedConeDivisor
import Proposal.GeometricGenericWeightedExterior

/-! The rational function field of the universal normalized sextic has exact
differential basis dx₂, dx₃, dw over its coefficient field. Consequently the
class of the specified weighted residue vanishes precisely when the universal
rational primitive exists. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeUniversal

open CycleQ2GenericWeightedExterior (Form volume exteriorD2)
open CycleQ2MonicWeightedPrimitiveIdentity (density)
open CycleQ2UniversalWeightedTransfer (UniversalWeightedPrimitiveExists)
open scoped CycleQ2WeightedConeUniversal

def coordinateBasis : Module.Basis (Fin 3) FunctionField Ω[FunctionField⁄Base] :=
  CycleQ2WeightedConeDifferentialBasis.basis spatial relativeDirection relativeDirection_spatial
    (fun _ _ h => spatial_ext h)

theorem coordinateBasis_apply (i : Fin 3) :
    coordinateBasis i = KaehlerDifferential.D Base FunctionField (spatial i) :=
  CycleQ2WeightedConeDifferentialBasis.basis_apply _ _ _ _ i

theorem coordinateBasis_repr_D (y : FunctionField) (i : Fin 3) :
    coordinateBasis.repr (KaehlerDifferential.D Base FunctionField y) i = relativeDirection i y :=
  CycleQ2WeightedConeDifferentialBasis.basis_repr_D _ _ _ _ y i

abbrev d₂ := exteriorD2 coordinateBasis relativeDirection
def topForm : Form Base FunctionField 3 :=
  density value affineEquation • volume coordinateBasis

theorem topForm_divisor_residue :
    topForm =
      CycleQ2WeightedConeVertex.onDivisor 1 (CycleQ2GeometricHodgeThreefold.equation coefficients)
        (value.comp (CycleQ2HodgeEuler.dehom 0).toRingHom) generic_normal generic_equation_zero
        (CycleQ2WeightedConeVertex.divisorResidue 1 (CycleQ2GeometricHodgeThreefold.equation coefficients)
          (CycleQ2WeightedConeVertex.coneNumerator Base)) • volume coordinateBasis := by
  rw [CycleQ2WeightedConeVertex.chart_divisor_density] <;> rfl

theorem d₂_scalar_wedge (a b c : FunctionField) :
    d₂ (a • exteriorPower.ιMulti FunctionField 2 (KaehlerDifferential.D Base FunctionField ∘ ![b,c])) =
      exteriorPower.ιMulti FunctionField 3 (KaehlerDifferential.D Base FunctionField ∘ ![a,b,c]) :=
  CycleQ2GenericWeightedExterior.exteriorD2_smul_exact_pair coordinateBasis relativeDirection
    coordinateBasis_repr_D relativeDirection_commute a b c

theorem d₂_unique (δ : Form Base FunctionField 2 →ₗ[Base] Form Base FunctionField 3)
    (hδ : ∀ a b c : FunctionField,
      δ (a • exteriorPower.ιMulti FunctionField 2 (KaehlerDifferential.D Base FunctionField ∘ ![b,c])) =
        exteriorPower.ιMulti FunctionField 3 (KaehlerDifferential.D Base FunctionField ∘ ![a,b,c])) :
    δ = d₂ :=
  CycleQ2GenericWeightedExterior.exteriorD2_unique coordinateBasis relativeDirection spatial
    coordinateBasis_apply coordinateBasis_repr_D relativeDirection_commute δ hδ

theorem four_forms_vanish : Subsingleton (Form Base FunctionField 4) :=
  CycleQ2GenericWeightedExterior.fourForm_subsingleton coordinateBasis

abbrev TopDeRham := Form Base FunctionField 3 ⧸ LinearMap.range d₂

def sourceClass : TopDeRham := Submodule.Quotient.mk topForm

theorem class_zero_iff_primitive : sourceClass = 0 ↔ UniversalWeightedPrimitiveExists := by
  have h : sourceClass = 0 ↔ ∃ η, d₂ η = topForm := Submodule.Quotient.mk_eq_zero _
  exact h.trans ((CycleQ2GenericWeightedExterior.exact_volume_iff_divergence
    coordinateBasis relativeDirection (density value affineEquation)).trans relative_primitive_iff)

end CycleQ2WeightedConeUniversal
end

#print axioms CycleQ2WeightedConeUniversal.coordinateBasis
#print axioms CycleQ2WeightedConeUniversal.class_zero_iff_primitive
