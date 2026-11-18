import Proposal.GeometricLiteralGenericSweptFamily
import Proposal.GeometricFieldRelativeForms
import Proposal.GeometricClosedExtRestriction

/-!
# The supported two-form map on the generic monic sextic

Pulling two-forms relative to the coefficient fraction field to the
scheme swept out by the original incidence family defines a map of
sheaves on the actual generic ambient. Its action on extensions by
the relative three-forms vanishes on the complementary open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GenericSweptExtSupport

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open CategoryTheory.Limits CycleQ2LiteralIncidenceRelativeCylinder
  CycleQ2LiteralIncidenceCylinderMap CycleQ2LiteralGenericSweptFamily
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2FieldRelativeForms (forms pull)

attribute [local instance] HasExt.standard

abbrev Threefold := ambient coefficient
abbrev structureMap := pullback.fst coefficient universalAmbientToBase
abbrev twoForms := forms structureMap 2
abbrev topForms := forms structureMap 3

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev swept := (relativeQ coefficient V t).image
abbrev inclusion : swept V t ⟶ Threefold := (relativeQ coefficient V t).imageι
abbrev complement : Threefold.Opens := CycleQ2ClosedExtRestriction.off (inclusion V t)
abbrev onSwept := forms (inclusion V t ≫ structureMap) 2
abbrev directImage := (Scheme.Modules.pushforward (inclusion V t)).obj (onSwept V t)

def coefficientsMap : twoForms ⟶ directImage V t := pull (inclusion V t) structureMap 2

/-- The generic correspondence coefficient vanishes on the actual open complement. -/
theorem directImage_off :
    IsZero ((Scheme.Modules.restrictFunctor (complement V t).ι).obj (directImage V t)) :=
  CycleQ2ClosedExtRestriction.pushforward_off_closed (inclusion V t) (onSwept V t)

/-- Contravariant Yoneda action of the Kähler two-form map, over the generic coefficient
field. -/
def supportedMap : Ext.{1} (directImage V t) topForms 2 →+ Ext.{1} twoForms topForms 2 :=
  (Ext.mk₀ (coefficientsMap V t)).precomp topForms (zero_add 2)

theorem supportedMap_off (e : Ext.{1} (directImage V t) topForms 2) :
    ((supportedMap V t) e).mapExactFunctor (Scheme.Modules.restrictFunctor (complement V t).ι) = 0 :=
  CycleQ2ClosedExtRestriction.supportedPrecomp_restrict (inclusion V t) (coefficientsMap V t) e

end CycleQ2GenericSweptExtSupport
end

#print axioms CycleQ2GenericSweptExtSupport.directImage_off
#print axioms CycleQ2GenericSweptExtSupport.supportedMap_off
