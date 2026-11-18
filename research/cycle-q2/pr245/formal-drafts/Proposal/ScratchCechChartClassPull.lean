import Proposal.GeometricLogarithmicChartDerivative
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Pullback from an affine chart to its function field on genuine exterior
three-forms modulo derivatives of exterior two-forms. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2.Cech.Chart

open CycleQ2LogarithmicPullback (Forms)
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2LogarithmicChartDerivative (pull pull_d)

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    {I J : Type} [Fintype I] [LinearOrder I] [Fintype J] [LinearOrder J]

abbrev ThreeFormQuotient (b : Module.Basis I R (KaehlerDifferential k R)) :=
  Forms k R 3 ⧸ (exteriorD b 2).range

variable (π : R →ₐ[k] S) (b : Module.Basis I R (KaehlerDifferential k R))
    (x : I → R) (hx : ∀ i, b i = KaehlerDifferential.D k R (x i))
    (c : Module.Basis J S (KaehlerDifferential k S))
    (y : J → S) (hy : ∀ i, c i = KaehlerDifferential.D k S (y i))

def pullClass : ThreeFormQuotient b →+ ThreeFormQuotient c :=
  let q := QuotientAddGroup.mk' (exteriorD c 2).range
  QuotientAddGroup.lift _ (q.comp (pull π 3).toAddMonoidHom) (by
    rintro z ⟨a,rfl⟩
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨pull π 2 a,pull_d π b x hx c y hy 2 a⟩)

@[simp] theorem pullClass_mk (z : Forms k R 3) :
    pullClass π b x hx c y hy (QuotientAddGroup.mk z) = QuotientAddGroup.mk (pull π 3 z) := rfl

/-- The vanishing of a chart class supplies an actual rational primitive in
the chosen field extension. -/
theorem pull_exact_of_class_zero (z : Forms k R 3)
    (hz : (QuotientAddGroup.mk z : ThreeFormQuotient b) = 0) :
    ∃ ξ : Forms k S 2, exteriorD c 2 ξ = pull π 3 z := by
  obtain ⟨a,ha⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz
  exact ⟨pull π 2 a, (pull_d π b x hx c y hy 2 a).trans (congrArg (pull π 3) ha)⟩

end CycleQ2.Cech.Chart
end
#print axioms CycleQ2.Cech.Chart.pullClass
