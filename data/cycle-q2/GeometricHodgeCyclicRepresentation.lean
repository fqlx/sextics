import Proposal.GeometricHodgeCyclicCohomology
import Proposal.GeometricSheafCohomologyScalar
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Complex-linear action of the cubic roots of unity on the moving Hodge group

The scheme action fixes the coefficient field. Its action on the native
second exterior sheaf commutes with multiplication by every complex number.
Finite Čech representatives carry that commutation to the full derived group.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicRepresentation
open CategoryTheory CategoryTheory.Abelian Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricHodgeThreefold CycleQ2HodgeCyclicAction CycleQ2HodgeCyclicCohomology
  CycleQ2GeometricSheafCohomologyScalar CycleQ2ExteriorPullComposition CycleQ2GeometricDifferentialSheaf
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne CycleQ2FiniteCechOrbitPullback
  CycleQ2GeometricSheafLocalIso CycleQ2CechTwoNaturality
open CycleQ2GenericSexticGradient (CoeffRing)
local instance (S : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from S)) := HasExt.standard _

variable (φ : CoeffRing →+* ℂ)
abbrev M := forms (threefold φ) (coeff φ) 2
private abbrev sc := scalarEnd (threefold φ).sheaf (coeff φ) (M φ)
local instance : Module ℂ (hodgeOne φ) := cohomologyModule (threefold φ).sheaf (coeff φ) (M φ) 1 ⊤

variable (z : ℂ) (hz : z^3=1)
private abbrev g := (action φ z hz).hom
private abbrev Λ := additivePull (g φ z hz) (coeff φ) (coeff φ)
    (compatible_over _ _ _ (action_overBase φ z hz)) 2

private theorem square (c : ℂ) :
    sc φ c ≫ Λ φ z hz = Λ φ z hz ≫ (TopCat.Sheaf.pushforward AddCommGrpCat (g φ z hz).base).map (sc φ c) := by
  ext V x
  let P := schemeExteriorPull (g φ z hz) (coeff φ) (coeff φ)
    (compatible_over _ _ _ (action_overBase φ z hz)) 2
  change P.val.app V (coefficientOn (threefold φ).sheaf (coeff φ) V.unop c • x) =
    coefficientOn (threefold φ).sheaf (coeff φ) ((g φ z hz) ⁻¹ᵁ V.unop) c • P.val.app V x
  exact ((CycleQ2LiteralAbelJacobiQPullback.onSections (g φ z hz) P V.unop).map_smulₛₗ _ x).trans
    (congrArg (fun a : Γ(threefold φ, (g φ z hz) ⁻¹ᵁ V.unop) => a • P.val.app V x)
      (compatible_over _ _ _ (action_overBase φ z hz) V.unop c))

theorem hodgeAction_smul (c : ℂ) (x : hodgeOne φ) :
    hodgeAction φ z hz (c • x) = c • hodgeAction φ z hz x := by
  let := toBase_proper φ
  let : CompactSpace (threefold φ) := (quasiCompact_iff_compactSpace (toBase φ)).mp inferInstance
  obtain ⟨t,U,hU,b,hb,rfl⟩ := CycleQ2HodgeCompactOneCocycles.representative (hodgeSheaf φ) x
  change CycleQ2LiteralAbelJacobiQPullbackDerived.pullH (g φ z hz).base (Λ φ z hz) 1
      ((cechOneClass U hU b hb).comp (Ext.mk₀ (sc φ c)) (add_zero 1)) =
    (CycleQ2LiteralAbelJacobiQPullbackDerived.pullH (g φ z hz).base (Λ φ z hz) 1
      (cechOneClass U hU b hb)).comp (Ext.mk₀ (sc φ c)) (add_zero 1)
  rw [cechOneClass_naturality, CycleQ2LiteralAbelJacobiQPullbackDerived.pullH_cech,
    CycleQ2LiteralAbelJacobiQPullbackDerived.pullH_cech, cechOneClass_naturality]
  congr 1
  exact pullOne_mapOne (g φ z hz).base U (sc φ c) (sc φ c) _ _ (square φ z hz c) b

def linearAction : Module.End ℂ (hodgeOne φ) where
  __ := hodgeAction φ z hz
  map_smul' := hodgeAction_smul φ z hz

def representation : rootsOfUnity 3 ℂ →* Module.End ℂ (hodgeOne φ) where
  toFun r := linearAction φ (r.val : ℂ) ((mem_rootsOfUnity' 3 r.val).mp r.property)
  map_one' := LinearMap.ext (hodgeAction_one φ)
  map_mul' r s := LinearMap.ext (fun x => (hodgeAction_comp φ (r.val : ℂ) (s.val : ℂ)
    ((mem_rootsOfUnity' 3 r.val).mp r.property) ((mem_rootsOfUnity' 3 s.val).mp s.property) x).symm)

end CycleQ2HodgeCyclicRepresentation
end

#print axioms CycleQ2HodgeCyclicRepresentation.hodgeAction_smul
#print axioms CycleQ2HodgeCyclicRepresentation.representation
