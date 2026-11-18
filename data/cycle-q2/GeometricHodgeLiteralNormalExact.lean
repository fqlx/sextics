import Proposal.GeometricHodgeNormalExact
import Proposal.GeometricHodgeThreefoldLiteralGradient

/-!
# The normal sequence on the literal smooth fiber at 57

At the specified incidence fiber, its own gradient supplies the local lifts
of the original normal map on every weight-one chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeLiteralNormalExact

open AlgebraicGeometry CategoryTheory Limits MvPolynomial CycleQ2HodgeEuler
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence CycleQ2HodgeEulerSheaf

theorem literal_conePartial_span (i : Fin 4) :
    Ideal.span (Set.range (conePartial literalEval i)) = ⊤ := by
  apply top_le_iff.mp
  rw [← literal_chartGradient_span i]
  apply Ideal.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨i.castSucc.succAbove j, partial_succAbove literalEval i j⟩

theorem literal_normal_additive_epi :
    Epi ((SheafOfModules.toSheaf (threefold literalEval).ringCatSheaf).map (normalMap literalEval)) :=
  normal_additive_epi_of_span literalEval literal_vertex_unit literal_conePartial_span

theorem literal_normal_shortExact : (normalSequence literalEval).ShortExact := by
  haveI : Epi (normalMap literalEval) :=
    Functor.epi_of_epi_map _ literal_normal_additive_epi
  exact { exact := ShortComplex.exact_kernel (normalMap literalEval) }

end CycleQ2HodgeLiteralNormalExact
end

#print axioms CycleQ2HodgeLiteralNormalExact.literal_normal_shortExact
