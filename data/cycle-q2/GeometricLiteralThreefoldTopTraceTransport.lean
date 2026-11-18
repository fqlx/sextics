import Proposal.GeometricLiteralThreefoldTopTrace
import Proposal.GeometricClosedEmbeddingSheafDescent
import Proposal.GeometricSheafCohomologyScalar

/-!
# Complex linearity of canonical cohomology transport on the fixed threefold

A scheme isomorphism over the complex point carries the locally restricted
complex constants to one another. Direct-image naturality transports this
identity to the structure sheaf's derived cohomology. Multiplication by the
global residue volume then gives the corresponding complex-linear
identification with top canonical cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldTopTraceTransport

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite TopologicalSpace
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSheafCohomologyScalar CycleQ2ClosedEmbeddingSheafExact
  CycleQ2ClosedEmbeddingCohomology CycleQ2ClosedEmbeddingSheafDescent
  CycleQ2LiteralThreefoldTopTrace
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2InjectiveCech (AbSheaf)

local instance (X : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _

abbrev unitModule (X : Scheme.{0}) := SheafOfModules.unit (ringSheaf X.sheaf)

variable {X Y : Scheme.{0}} (e : X ≅ Y) (f : Y ⟶ Spec (CommRingCat.of ℂ))

private theorem structurePushIso_scalar (z : ℂ) :
    scalarEnd Y.sheaf (schemeCoefficient f) (unitModule Y) z ≫ (structurePushIso e).hom =
      (structurePushIso e).hom ≫ (push e.hom.base).map
        (scalarEnd X.sheaf (schemeCoefficient (e.hom ≫ f)) (unitModule X) z) := by
  ext U x
  let a : Γ(Y,U.unop) := coefficientOn Y.sheaf (schemeCoefficient f) U.unop z
  let y : Γ(Y,U.unop) := x
  let b : Γ(X,e.hom ⁻¹ᵁ U.unop) :=
    coefficientOn X.sheaf (schemeCoefficient (e.hom ≫ f)) (e.hom ⁻¹ᵁ U.unop) z
  change e.hom.app U.unop (a * y) = b * e.hom.app U.unop y
  exact ((e.hom.app U.unop).hom.map_mul a y).trans
    (congrArg (fun c : Γ(X,e.hom ⁻¹ᵁ U.unop) => c * e.hom.app U.unop y)
      (coefficientOn_app e.hom f U.unop z))

private theorem structurePushIso_inv_scalar (z : ℂ) :
    (push e.hom.base).map (scalarEnd X.sheaf (schemeCoefficient (e.hom ≫ f)) (unitModule X) z) ≫
      (structurePushIso e).inv =
    (structurePushIso e).inv ≫ scalarEnd Y.sheaf (schemeCoefficient f) (unitModule Y) z := by
  apply (cancel_epi (structurePushIso e).hom).mp
  rw [← Category.assoc, ← structurePushIso_scalar, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

/-- Derived cohomology transport along a complex scheme isomorphism preserves
the complex action of the structure sheaf in every degree. -/
theorem structureCohomology_scalar (n : ℕ) (z : ℂ) (x : (structureAdditiveSheaf X).H' n ⊤) :
    structureCohomology e n (cohomologyScalar X.sheaf (schemeCoefficient (e.hom ≫ f))
      (unitModule X) n ⊤ z x) =
    cohomologyScalar Y.sheaf (schemeCoefficient f) (unitModule Y) n ⊤ z
      (structureCohomology e n x) := by
  let a := scalarEnd X.sheaf (schemeCoefficient (e.hom ≫ f)) (unitModule X) z
  let b := scalarEnd Y.sheaf (schemeCoefficient f) (unitModule Y) z
  let p := pushHEquiv e.hom.base e.hom.isClosedEmbedding (structureAdditiveSheaf X) n
  let k := (structurePushIso e).inv
  change (p (x.comp (Ext.mk₀ a) (add_zero n))).comp (Ext.mk₀ k) (add_zero n) =
    ((p x).comp (Ext.mk₀ k) (add_zero n)).comp (Ext.mk₀ b) (add_zero n)
  rw [show p (x.comp (Ext.mk₀ a) (add_zero n)) =
    (p x).comp (Ext.mk₀ ((push e.hom.base).map a)) (add_zero n) from
      pushHEquiv_natural e.hom.base e.hom.isClosedEmbedding a n x]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg (fun u => (p x).comp (Ext.mk₀ u) (add_zero n)) (structurePushIso_inv_scalar e f z)

open CycleQ2GeometricHodgeThreefold (threefold toBase)
open CycleQ2GeometricHodgeThreefoldIncidence (literalEval literalIso literalIso_overComplex)
open CycleQ2LiteralThreefoldCanonicalVolume (threeForms coeff)
open CycleQ2LiteralThreefoldCanonicalFrame (volumeIso)
open CycleQ2LiteralThreefoldHodgeCech (Threefold)
open CycleQ2GeometricModuleLocalIso (addSheaf)

abbrev sourceCoeff := schemeCoefficient (toBase literalEval)

theorem toCanonical_scalar (z : ℂ) (x : (structureAdditiveSheaf (threefold literalEval)).H' 3 ⊤) :
    toCanonical (cohomologyScalar (threefold literalEval).sheaf sourceCoeff (unitModule (threefold literalEval)) 3 ⊤ z x) =
    cohomologyScalar Threefold.sheaf coeff threeForms 3 ⊤ z (toCanonical x) := by
  have h := structureCohomology_scalar literalIso CycleQ2LiteralThreefoldCanonicalVolume.structural 3 z x
  rw [literalIso_overComplex] at h
  exact (congrArg (canonicalCohomology 3) h).trans
    (cohomologyMap_scalar Threefold.sheaf coeff (unitModule Threefold) volumeIso.hom
      3 ⊤ z (structureCohomology literalIso 3 x))

/-- The actual identification from the monic sextic to its marked canonical
bundle in degree three, with its complex linearity. -/
def toCanonicalLinearEquiv :
    letI : Module ℂ ((structureAdditiveSheaf (threefold literalEval)).H' 3 ⊤) :=
      cohomologyModule _ sourceCoeff (unitModule (threefold literalEval)) 3 ⊤
    letI : Module ℂ ((addSheaf threeForms).H' 3 ⊤) := cohomologyModule _ coeff threeForms 3 ⊤
    (structureAdditiveSheaf (threefold literalEval)).H' 3 ⊤ ≃ₗ[ℂ] (addSheaf threeForms).H' 3 ⊤ := by
  letI : Module ℂ ((structureAdditiveSheaf (threefold literalEval)).H' 3 ⊤) :=
    cohomologyModule _ sourceCoeff (unitModule (threefold literalEval)) 3 ⊤
  letI : Module ℂ ((addSheaf threeForms).H' 3 ⊤) := cohomologyModule _ coeff threeForms 3 ⊤
  exact { toAddEquiv := toCanonical, map_smul' := toCanonical_scalar }

end CycleQ2LiteralThreefoldTopTraceTransport

#print axioms CycleQ2LiteralThreefoldTopTraceTransport.structureCohomology_scalar
#print axioms CycleQ2LiteralThreefoldTopTraceTransport.toCanonicalLinearEquiv
