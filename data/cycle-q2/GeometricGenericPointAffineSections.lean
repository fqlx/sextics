import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Normalization

/-!
# The fraction field on the inverse image of a nonempty affine under the generic point

The actual map on sections induced by the generic residue-field point factors
as the germ into the function field followed by a ring isomorphism. Thus the
native section ring used by scheme normalization is the affine fraction field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GenericPointAffineSections

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
variable (X : Scheme.{u}) [IsIntegral X]

abbrev point := X.fromSpecResidueField (genericPoint X)

abbrev pointScheme := Spec (X.residueField (genericPoint X))

theorem residue_isIso : IsIso (X.residue (genericPoint X)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩

variable (U : X.Opens) [Nonempty U]

private theorem generic_mem : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

private theorem stalkPreimage_eq_top :
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro s _
  change (X.fromSpecStalk (genericPoint X)) s ∈ U
  letI : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  rw [Subsingleton.elim s (IsLocalRing.closedPoint X.functionField), Scheme.fromSpecStalk_closedPoint]
  exact generic_mem X U

private def chartIsoHom : X.functionField ⟶ Γ(pointScheme X, point X ⁻¹ᵁ U) :=
  (Scheme.ΓSpecIso X.functionField).inv ≫
    (Spec X.functionField).presheaf.map (homOfLE
      (show (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
      (Spec.map (X.residue (genericPoint X))).app ((X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)

private instance : IsIso (chartIsoHom X U) := by
  have := residue_isIso X
  have := homOfLE_isIso_of_eq (show (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ≤ ⊤ from le_top)
    (stalkPreimage_eq_top X U)
  unfold chartIsoHom
  infer_instance

def chartIso : X.functionField ≅ Γ(pointScheme X, point X ⁻¹ᵁ U) := asIso (chartIsoHom X U)

@[reassoc] theorem germ_chartIso :
    X.germToFunctionField U ≫ (chartIso X U).hom = (point X).app U := by
  change _ = (Spec.map (X.residue (genericPoint X)) ≫ X.fromSpecStalk (genericPoint X)).app U
  rw [Scheme.Hom.comp_app, Scheme.fromSpecStalk_app (generic_mem X U)]
  simp only [chartIso, asIso_hom, chartIsoHom, Category.assoc]

theorem native_isField : IsField Γ(pointScheme X, point X ⁻¹ᵁ U) :=
  (chartIso X U).symm.commRingCatIsoToRingEquiv.isField (Field.toIsField X.functionField)

def chartAlgEquiv :
    let := ((point X).app U).hom.toAlgebra
    X.functionField ≃ₐ[Γ(X,U)] Γ(pointScheme X, point X ⁻¹ᵁ U) := by
  let := ((point X).app U).hom.toAlgebra
  exact { (chartIso X U).commRingCatIsoToRingEquiv with
    commutes' := fun a => congrArg (fun f : Γ(X,U) ⟶ _ => f a) (germ_chartIso X U) }

theorem native_isFractionRing (hU : IsAffineOpen U) :
    let := ((point X).app U).hom.toAlgebra
    IsFractionRing Γ(X,U) Γ(pointScheme X, point X ⁻¹ᵁ U) := by
  let := ((point X).app U).hom.toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsFractionRing.of_algEquiv (chartAlgEquiv X U)

end CycleQ2GenericPointAffineSections
end

#print axioms CycleQ2GenericPointAffineSections.native_isFractionRing
