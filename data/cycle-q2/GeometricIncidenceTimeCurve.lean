import Proposal.GeometricIncidenceEtaleParameter
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth

/-!
# A nonempty smooth parameter curve over the generic sextic field

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request.

The parameter algebra constructed in GeometricIncidenceEtaleParameter is
étale over C[time, sextic coefficients]. The actual inclusion of the sextic
coefficient ring is identified here with the coefficient inclusion in a
polynomial ring with one variable. Consequently the same parameter space
is smooth of relative dimension one over the full sextic coefficient space.

Flatness and nontriviality show that its generic fiber does not disappear.
The resulting affine scheme is a nonempty smooth curve over the generic
sextic field. This is the curve parametrizing the motion of the sections;
smoothness of the projective cycle fibers is a different assertion.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceTimeCurve

open MvPolynomial CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceNormalForm CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceEtaleParameter
open scoped TensorProduct

abbrev SexticRing := MvPolynomial (FullInvariantIndex 6) ℂ
abbrev TimeLineRing := MvPolynomial Unit SexticRing
abbrev GenericSexticField := FractionRing SexticRing

/-- This inclusion preserves each original independent sextic coefficient. -/
def sexticToTrace : SexticRing →+* TraceRing :=
  MvPolynomial.rename (Sum.inr : FullInvariantIndex 6 → Unit ⊕ FullInvariantIndex 6)

def traceAsTimeLine : TraceRing ≃+* TimeLineRing :=
  MvPolynomial.sumRingEquiv ℂ Unit (FullInvariantIndex 6)

theorem traceAsTimeLine_comp_sextic :
    traceAsTimeLine.toRingHom.comp sexticToTrace = (C : SexticRing →+* TimeLineRing) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [traceAsTimeLine, sexticToTrace]
  · intro j
    simp [traceAsTimeLine, sexticToTrace]

theorem sexticToTrace_eq :
    sexticToTrace = traceAsTimeLine.symm.toRingHom.comp (C : SexticRing →+* TimeLineRing) := by
  ext p
  apply traceAsTimeLine.injective
  change traceAsTimeLine (sexticToTrace p) =
    traceAsTimeLine (traceAsTimeLine.symm (C p))
  rw [traceAsTimeLine.apply_symm_apply]
  exact RingHom.congr_fun traceAsTimeLine_comp_sextic p

@[simp] theorem traceAsTimeLine_time : traceAsTimeLine traceParameter = X () := by
  simp [traceAsTimeLine, traceParameter]

@[simp] theorem traceAsTimeLine_sextic (j : FullInvariantIndex 6) :
    traceAsTimeLine (sexticParameter j) = C (X j) := by
  simp [traceAsTimeLine, sexticParameter]

/-! ## The one-variable presentation, with no relations -/

private def timeLinePrePresentation :
    Algebra.PreSubmersivePresentation SexticRing TimeLineRing Unit Empty where
  toPresentation :=
    { toGenerators := Algebra.Generators.mvPolynomial SexticRing Unit
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  map := Empty.elim
  map_inj := by intro a; exact a.elim

private theorem timeLinePrePresentation_jacobian :
    timeLinePrePresentation.jacobian = 1 := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp

private def timeLinePresentation :
    Algebra.SubmersivePresentation SexticRing TimeLineRing Unit Empty where
  toPreSubmersivePresentation := timeLinePrePresentation
  jacobian_isUnit := by rw [timeLinePrePresentation_jacobian]; exact isUnit_one

theorem timeLine_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 1 SexticRing TimeLineRing := by
  apply timeLinePresentation.isStandardSmoothOfRelativeDimension
  change Nat.card Unit - Nat.card Empty = 1
  norm_num [Nat.card_eq_fintype_card]

theorem sexticToTrace_standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension 1 sexticToTrace := by
  have hc : RingHom.IsStandardSmoothOfRelativeDimension 1
      (C : SexticRing →+* TimeLineRing) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr timeLine_standardSmooth
  rw [sexticToTrace_eq]
  simpa only [Nat.zero_add] using
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv traceAsTimeLine.symm).comp hc

def sexticToParameter : SexticRing →+* ParameterAlgebra :=
  (algebraMap TraceRing ParameterAlgebra).comp sexticToTrace

@[simp] theorem sexticToParameter_X (j : FullInvariantIndex 6) :
    sexticToParameter (X j) =
      algebraMap TraceRing ParameterAlgebra (sexticParameter j) := by
  simp [sexticToParameter, sexticToTrace, sexticParameter]

theorem sexticToParameter_standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension 1 sexticToParameter := by
  have he : RingHom.IsStandardSmoothOfRelativeDimension 0
      (algebraMap TraceRing ParameterAlgebra) :=
    RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp
      (RingHom.etale_algebraMap.mpr parameter_etale)
  simpa only [Nat.zero_add] using he.comp sexticToTrace_standardSmooth

instance parameter_sexticAlgebra : Algebra SexticRing ParameterAlgebra :=
  sexticToParameter.toAlgebra

instance parameter_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 1 SexticRing ParameterAlgebra :=
  sexticToParameter_standardSmooth

instance parameter_standardSmooth_ungraded :
    Algebra.IsStandardSmooth SexticRing ParameterAlgebra :=
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1

instance parameter_flat_overSextics : Module.Flat SexticRing ParameterAlgebra := inferInstance

def sexticBase : Scheme := Spec (CommRingCat.of SexticRing)

def parameterToSextics : parameterScheme ⟶ sexticBase :=
  Spec.map (CommRingCat.ofHom sexticToParameter)

theorem parameterToSextics_smooth_relative_one :
    SmoothOfRelativeDimension 1 parameterToSextics := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    sexticToParameter sexticToParameter_standardSmooth

/-! ## A nonempty generic fiber, retaining the actual parameter algebra -/

abbrev GenericTimeAlgebra := GenericSexticField ⊗[SexticRing] ParameterAlgebra

instance genericTime_nontrivial : Nontrivial GenericTimeAlgebra :=
  Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right
    SexticRing GenericSexticField ParameterAlgebra (IsFractionRing.injective _ _)

instance genericTime_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 1 GenericSexticField GenericTimeAlgebra :=
  inferInstance

def genericTimeCurve : Scheme := Spec (CommRingCat.of GenericTimeAlgebra)

def genericTimeCurveToField : genericTimeCurve ⟶ Spec (CommRingCat.of GenericSexticField) :=
  Spec.map (CommRingCat.ofHom (algebraMap GenericSexticField GenericTimeAlgebra))

theorem genericTimeCurve_nonempty : Nonempty genericTimeCurve :=
  inferInstanceAs (Nonempty (PrimeSpectrum GenericTimeAlgebra))

theorem genericTimeCurve_smooth_relative_one :
    SmoothOfRelativeDimension 1 genericTimeCurveToField := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
    genericTime_standardSmooth

/-- The generic curve is obtained from the same incidence parameter space. -/
def genericTimeCurveToParameters : genericTimeCurve ⟶ parameterScheme :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : ParameterAlgebra →ₐ[SexticRing] GenericTimeAlgebra).toRingHom)

theorem genericTimeCurve_overSextics :
    genericTimeCurveToParameters ≫ parameterToSextics =
      genericTimeCurveToField ≫ Spec.map
        (CommRingCat.ofHom (algebraMap SexticRing GenericSexticField)) := by
  rw [genericTimeCurveToParameters, parameterToSextics, genericTimeCurveToField,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext p
  change Algebra.TensorProduct.includeRight
      (algebraMap SexticRing ParameterAlgebra p) =
    algebraMap GenericSexticField GenericTimeAlgebra (algebraMap SexticRing GenericSexticField p)
  rw [AlgHom.commutes]
  exact IsScalarTower.algebraMap_apply SexticRing GenericSexticField GenericTimeAlgebra p

end CycleQ2IncidenceTimeCurve

#print axioms CycleQ2IncidenceTimeCurve.parameterToSextics_smooth_relative_one
#print axioms CycleQ2IncidenceTimeCurve.genericTimeCurve_nonempty
#print axioms CycleQ2IncidenceTimeCurve.genericTimeCurve_smooth_relative_one
#print axioms CycleQ2IncidenceTimeCurve.genericTimeCurve_overSextics

end
