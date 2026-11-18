import Proposal.GeometricIncidenceProjectorTestSpread
import Proposal.GeometricIncidenceMarkedObstructionNonzero
import Proposal.GeometricIncidenceProjectorLiftObstruction

/-!
# The nonzero incidence obstruction near the marked sextic

For each independent section vector, choose the original smooth proper family
of projective curves over the time parameter. On one coefficient neighborhood
of the marked sextic, every complex coefficient has a time point with nonzero
projector residue. The generic coefficient has such a point over a finite
étale extension. At each point the actual projector transition lifts are
incompatible.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IncidenceNonzeroTestLocus

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceSeedFiberCover CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceGenericModel
  CycleQ2IncidenceProjectorTestSpread CycleQ2IncidenceRelativeProjectorSpecialization
  CycleQ2IncidenceProjectorLiftObstruction CycleQ2RelativeCanonicalLaurentTrace
  CycleQ2IncidenceMarkedObstructionNonzero

/-- Both conclusions concern the same specialized incidence matrix and its edge transitions. -/
def Obstructed {L : Type} [Field L] (f : ParameterAlgebra →+* L) : Prop :=
  residue (cubicFiber f) (sexticFiber f) (fiberCup f) ≠ 0 ∧ IsEmpty (CompatibleLift f)

private theorem obstructed_of_residue {L : Type} [Field L] (f : ParameterAlgebra →+* L)
    (h : residue (cubicFiber f) (sexticFiber f) (fiberCup f) ≠ 0) : Obstructed f :=
  ⟨h, no_compatible_lift f (by rwa [← fiber_residue])⟩

/-- The true incidence obstruction occurs throughout a marked coefficient open and
at a finite étale generic parameter point in the same smooth proper curve family. -/
theorem nonzero_in_literal_family (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      SmoothOfRelativeDimension 1 (timeMap toRaw V) ∧
      SmoothOfRelativeDimension 1 (curveMap toRaw V t) ∧ IsProper (curveMap toRaw V t) ∧
      Surjective (curveMap toRaw V t) ∧
      (∃ D : monicBase.Opens, seedPoint default ∈ D ∧
        ∀ b : Spec (CommRingCat.of ℂ) ⟶ monicBase, b default ∈ D →
          ∃ s : Spec (CommRingCat.of ℂ) ⟶ Time toRaw V, s ≫ timeMap toRaw V = b ∧
            Obstructed (evalComplex V s)) ∧
      ∃ x : TimeFiber V, IsClosed {x} ∧
        IsFinite ((TimeFiber V).fromSpecResidueField x ≫ inclusion V ≫ projection V) ∧
        Etale ((TimeFiber V).fromSpecResidueField x ≫ inclusion V ≫ projection V) ∧
        Obstructed (evalGeneric V x) := by
  have : IrreducibleSpace monicBase := inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  obtain ⟨V, hV, htime, hcurve, _, hp, hs, _, _, _⟩ :=
    spread_of_independent toRaw seedPoint seedPoint_toRaw t hi
  obtain ⟨D, hd, hD⟩ := complex_nonzero_neighborhood V hV regularCoefficient_at_mark_ne_zero
  obtain ⟨x, hx, hf, he, hr⟩ := generic_nonzero V hV regularCoefficient_at_mark_ne_zero
  refine ⟨V, hV, htime, hcurve, hp, hs, ⟨D, hd, ?_⟩, x, hx, hf, he, obstructed_of_residue _ hr⟩
  intro b hb
  obtain ⟨s, hs, hr⟩ := hD b hb
  exact ⟨s, hs, obstructed_of_residue _ hr⟩

end CycleQ2IncidenceNonzeroTestLocus
end

#print axioms CycleQ2IncidenceNonzeroTestLocus.nonzero_in_literal_family
