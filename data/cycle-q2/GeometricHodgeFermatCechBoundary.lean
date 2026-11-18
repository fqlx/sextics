import Proposal.GeometricHodgeFermatNormalLifts
import Proposal.GeometricHodgeNormalConnectingCech
import Proposal.GeometricHodgeThreefoldProper

/-!
# Čech representatives for normal deformations of the Fermat threefold

Differences of the four explicit homogeneous coordinate lifts are sections
of the actual normal kernel on the six pair intersections. Their Čech
classes are the connecting classes of the original global O(6) sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatCechBoundary

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace CategoryTheory.Abelian
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeEulerSheaf CycleQ2HodgeFermatNormalLifts CycleQ2HodgeNormalCohomology
open CycleQ2SeedSectionSheafLimits (sectionKernelEquiv sectionKernelEquiv_val sectionKernelEquiv_symm_val)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)
open CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteInjectiveCech
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2CechTwoToDerived (sectionExtZero)
open CycleQ2GeometricConeCech.HZero (sectionsEquiv)
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

theorem smooth_parameter : IsUnit (ψ goodParameter) := by
  rw [show ψ goodParameter = 1 from goodParameter_seed]
  exact isUnit_one

theorem vertex_unit : IsUnit (ψ vertexCoefficient) := by
  rw [show ψ vertexCoefficient = 1 from seed_vertexCoefficient]
  exact isUnit_one

theorem cover_eq_top : (⨆ i, U ψ i) = ⊤ := coordinateOpens_cover ψ vertex_unit

abbrev F := Add ψ (rawTangent ψ)
abbrev lifts (p : grade ψ 6) (i : Fin 4) := lift i (U ψ i) le_rfl p.val p.property

def difference (p : grade ψ 6) (i j : Fin 4) (W : (threefold ψ).Opens)
    (hi : W ≤ U ψ i) (hj : W ≤ U ψ j) : Γ(rawTangent ψ,W) :=
  (sectionKernelEquiv (normalMap ψ) W).symm
    ⟨lift j W hj p.val p.property - lift i W hi p.val p.property, by
      change (normalMap ψ).app W (_ - _) = 0
      rw [map_sub, lift_normal, lift_normal, sub_self]⟩

theorem difference_val (p : grade ψ 6) (i j : Fin 4) (W : (threefold ψ).Opens)
    (hi : W ≤ U ψ i) (hj : W ≤ U ψ j) :
    (kernel.ι (normalMap ψ)).app W (difference p i j W hi hj) =
      lift j W hj p.val p.property - lift i W hi p.val p.property :=
  sectionKernelEquiv_symm_val (normalMap ψ) W _

private abbrev sectionOf (p : grade ψ 6) := homogeneousSection ψ p.val p.property ⊤

private theorem lifted (p : grade ψ 6) (i : Fin 4) :
    (normalMap ψ).app (U ψ i) (lifts p i) = moduleRes (twist ψ 6) le_top (sectionOf p) := by
  change (normalMap ψ).app _ (lift i _ _ _ _) =
    moduleRes (twist ψ 6) le_top (homogeneousSection ψ p.val p.property ⊤)
  rw [lift_normal, homogeneousSection_restrict]

def cocycle (p : grade ψ 6) : One F (U ψ) :=
  CycleQ2HodgeNormalConnectingCech.cocycle ψ (U ψ) (sectionOf p) (lifts p) (lifted p)

theorem edge (p : grade ψ 6) (i j : Fin 4) (W : (threefold ψ).Opens)
    (hi : W ≤ U ψ i) (hj : W ≤ U ψ j) :
    edgeValue F (U ψ) (cocycle p) i j W hi hj = difference p i j W hi hj := by
  rw [cocycle, CycleQ2HodgeNormalConnectingCech.edge]
  apply CycleQ2HodgeNormalConnectingCech.inclusion_injective
  rw [CycleQ2HodgeNormalConnectingCech.difference_val, difference_val]
  change moduleRes (raw ψ) hj (lift j _ _ _ _) - moduleRes (raw ψ) hi (lift i _ _ _ _) = _
  rw [lift_restrict, lift_restrict]

theorem closed (p : grade ψ 6) : IsOneCocycle F (U ψ) (cocycle p) :=
  CycleQ2HodgeNormalConnectingCech.closed ψ (U ψ) (sectionOf p) (lifts p) (lifted p)

theorem cechClass (p : grade ψ 6) :
    cechOneClass (U ψ) cover_eq_top (cocycle p) (closed p) =
      connecting ψ smooth_parameter (homogeneousSection ψ p.val p.property ⊤) :=
  CycleQ2HodgeNormalConnectingCech.cechClass ψ (U ψ) (sectionOf p) (lifts p) (lifted p)
    smooth_parameter cover_eq_top

end CycleQ2HodgeFermatCechBoundary
end
#print axioms CycleQ2HodgeFermatCechBoundary.cechClass
