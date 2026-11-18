import Proposal.GeometricHodgeCyclicAction
import Proposal.GeometricHodgeCompactOneCocycles
import Proposal.GeometricHodgeThreefoldProper
import Proposal.GeometricExteriorPullComposition

/-!
# The cyclic group acts on the moving two-form cohomology

Pullback acts through the exterior square of the universal complex
differential. Finite Čech representatives on the compact threefold
identify composition on every derived degree-one class.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicCohomology

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricExteriorSheaf
open CycleQ2LiteralAbelJacobiQPullback (exteriorPull)
open CycleQ2ExteriorPullComposition CycleQ2FiniteCechOrbitPullback CycleQ2FiniteCechHOne
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2GeometricSheafLocalIso
  CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient CycleQ2HodgeCyclicAction

attribute [local instance] CycleQ2GeometricExteriorSheaf.exteriorObjectModule

local instance (S : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from S)) := HasExt.standard _

section Identity
variable (S : Scheme.{0}) (c : ℂ →+* Γ(S,⊤)) (h : compatible (𝟙 S) c c)

theorem exterior_id (n : ℕ) :
    schemeExteriorPull (𝟙 S) c c h n = (Scheme.Modules.pushforwardId S).inv.app _ := by
  have hd : (Scheme.Modules.pushforwardId S).inv.app _ = schemeDifferentialMap (𝟙 S) c c h :=
    schemeDifferentialMap_unique (𝟙 S) c c h _ (fun _ _ => rfl)
  apply (exteriorSheafHomEquiv S.sheaf (differentialSheaf S.sheaf c).val n _).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  change (exteriorPull (𝟙 S) (schemeDifferentialMap (𝟙 S) c c h) n).val.app U
    (exteriorSection S.sheaf (differentialSheaf S.sheaf c).val n U.unop x) = _
  rw [CycleQ2LiteralAbelJacobiQPullback.exteriorPull_section]
  apply congrArg (exteriorSection S.sheaf (differentialSheaf S.sheaf c).val n U.unop)
  apply exteriorMap_identity
  · exact fun _ => rfl
  · intro v
    change (schemeDifferentialMap (𝟙 S) c c h).val.app U v = v
    rw [← hd]
    rfl

end Identity

variable (φ : CoeffRing →+* ℂ)
abbrev coeff := schemeCoefficient (toBase φ)
abbrev hodgeSheaf := additiveForms (threefold φ) (coeff φ) 2
abbrev hodgeOne := (hodgeSheaf φ).H' 1 ⊤

private theorem over_compatible (g : threefold φ ⟶ threefold φ) (hg : g ≫ toBase φ = toBase φ) :
    compatible g (coeff φ) (coeff φ) := by
  intro U a
  rw [coefficientOn_app, hg]

def mapH (g : threefold φ ⟶ threefold φ) (hg : g ≫ toBase φ = toBase φ) :
    hodgeOne φ →+ hodgeOne φ :=
  CycleQ2LiteralAbelJacobiQPullbackDerived.pullH g.base
    (additivePull g (coeff φ) (coeff φ) (over_compatible φ g hg) 2) 1

private theorem mapH_congr {f g : threefold φ ⟶ threefold φ} (e : f = g)
    (hf : f ≫ toBase φ = toBase φ) (hg : g ≫ toBase φ = toBase φ) :
    mapH φ f hf = mapH φ g hg := by subst g; rfl

private theorem isCompact : CompactSpace (threefold φ) := by
  letI := toBase_proper φ
  exact (quasiCompact_iff_compactSpace (toBase φ)).mp inferInstance

theorem mapH_comp (f g : threefold φ ⟶ threefold φ)
    (hf : f ≫ toBase φ = toBase φ) (hg : g ≫ toBase φ = toBase φ)
    (hfg : (f ≫ g) ≫ toBase φ = toBase φ) (x : hodgeOne φ) :
    mapH φ (f ≫ g) hfg x = mapH φ f hf (mapH φ g hg x) := by
  letI := isCompact φ
  obtain ⟨t,U,hU,a,ha,rfl⟩ := CycleQ2HodgeCompactOneCocycles.representative (hodgeSheaf φ) x
  exact pullH_comp_cech f g (coeff φ) (coeff φ) (coeff φ) (over_compatible φ f hf)
    (over_compatible φ g hg) 2 U a hU ha

theorem mapH_id (x : hodgeOne φ) : mapH φ (𝟙 _) (Category.id_comp _) x = x := by
  letI := isCompact φ
  obtain ⟨t,U,hU,a,ha,rfl⟩ := CycleQ2HodgeCompactOneCocycles.representative (hodgeSheaf φ) x
  unfold mapH
  rw [CycleQ2LiteralAbelJacobiQPullbackDerived.pullH_cech]
  change cechOneClass U _ _ _ = cechOneClass U hU a ha
  congr 1
  funext i j
  change ((schemeExteriorPull (𝟙 _) _ _ _ 2).val.app _ (a i j)) = a i j
  rw [exterior_id]
  rfl

def hodgeAction (z : ℂ) (hz : z^3=1) : hodgeOne φ →+ hodgeOne φ :=
  mapH φ (action φ z hz).hom (action_overBase φ z hz)

theorem hodgeAction_comp (z w : ℂ) (hz : z^3=1) (hw : w^3=1) (x : hodgeOne φ) :
    hodgeAction φ z hz (hodgeAction φ w hw x) =
      hodgeAction φ (z*w) (CycleQ2LiteralOrbitAction.cubeRoot_mul hz hw) x := by
  let g := (action φ z hz).hom
  let k := (action φ w hw).hom
  have h : (g ≫ k) ≫ toBase φ = toBase φ := by
    dsimp [g, k]
    rw [Category.assoc, action_overBase, action_overBase]
  exact (mapH_comp φ g k (action_overBase φ z hz) (action_overBase φ w hw) h x).symm.trans
    (DFunLike.congr_fun (mapH_congr φ (action_comp φ z hz w hw) h (action_overBase φ _ _)) x)

theorem hodgeAction_one (x : hodgeOne φ) : hodgeAction φ 1 (one_pow 3) x = x :=
  (DFunLike.congr_fun (mapH_congr φ (action_one φ) (action_overBase φ _ _) (Category.id_comp _)) x).trans
    (mapH_id φ x)

end CycleQ2HodgeCyclicCohomology
end
#print axioms CycleQ2HodgeCyclicCohomology.hodgeAction_comp
#print axioms CycleQ2HodgeCyclicCohomology.hodgeAction_one
