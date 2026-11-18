import Proposal.GeometricIncidenceProjectiveProper
import Proposal.GeometricLiteralIncidenceCylinderMap

/-!
# Properness of the universal weighted sextic and its coefficient changes

The graded cone is finitely generated over its degree-zero part. Every
degree-zero class comes from the original coefficients, so the proper
Proj structure morphism gives properness over the full sextic base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralRelativeAmbientProper

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart CycleQ2IncidenceFamilyContainment
  CycleQ2LiteralIncidenceCylinderMap

theorem sexticCoefficient_surjective {S : Type} [CommRing S] [Algebra ℂ S]
    (y : ParameterIndex → S) : Function.Surjective (algebraMap S (sexticGrade y 0)) := by
  rintro ⟨q, hq⟩
  obtain ⟨p,hp,rfl⟩ := hq
  refine ⟨p.coeff 0, Subtype.ext ?_⟩
  change Ideal.Quotient.mk (sexticIdeal y) (C (p.coeff 0)) = Ideal.Quotient.mk (sexticIdeal y) p
  exact congrArg (Ideal.Quotient.mk (sexticIdeal y))
    (CycleQ2IncidenceProjectiveProper.polynomialGrade_zero_eq_C p hp).symm

theorem weightedThreefoldToBase_proper {S : Type} [CommRing S] [Algebra ℂ S]
    (y : ParameterIndex → S) : IsProper (weightedThreefoldToBase y) := by
  let : Algebra.FiniteType S (CycleQ2IncidenceFamilyContainment.SexticRing y) := inferInstance
  let : IsScalarTower S (sexticGrade y 0) (CycleQ2IncidenceFamilyContainment.SexticRing y) :=
    ⟨fun a b c => by
      change (a • (b : CycleQ2IncidenceFamilyContainment.SexticRing y)) * c = a • ((b : _) * c)
      exact smul_mul_assoc a (b : CycleQ2IncidenceFamilyContainment.SexticRing y) c⟩
  let : Algebra.FiniteType (sexticGrade y 0) (CycleQ2IncidenceFamilyContainment.SexticRing y) :=
    Algebra.FiniteType.of_restrictScalars_finiteType S _ _
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (sexticGrade y 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (sexticCoefficient_surjective y)
  unfold weightedThreefoldToBase
  infer_instance

theorem universalAmbientToBase_proper : IsProper universalAmbientToBase :=
  weightedThreefoldToBase_proper universalPoint

theorem ambient_proper {B : Scheme} (i : B ⟶ CycleQ2IncidenceTimeCurve.sexticBase) :
    IsProper (pullback.fst i universalAmbientToBase) := by
  let := universalAmbientToBase_proper
  infer_instance

end CycleQ2LiteralRelativeAmbientProper

#print axioms CycleQ2LiteralRelativeAmbientProper.ambient_proper
