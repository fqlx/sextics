import Proposal.GeometricHodgeFermatCechBoundary
import Proposal.GeometricHodgeEulerTangentRepresentatives
import Proposal.GeometricHodgeFermatYukawaRows

/-!
# Intrinsic tangent cocycles on the Fermat fiber

The map from the kernel of the homogeneous gradient to the relative tangent
sheaf transports the explicit normal connecting cocycle. On the full
fourfold overlap its three evaluated affine coordinates are the rows of the
Fermat determinant.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatTangentCochain

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace CategoryTheory.Abelian
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeTwistRatios CycleQ2HodgeEulerSheaf
open CycleQ2HodgeFermatNormalLifts CycleQ2HodgeFermatCechBoundary
open CycleQ2HodgeNormalCohomology CycleQ2HodgeEulerTangentSheaf (tangent)
open CycleQ2HodgeEulerTangentRepresentatives (intrinsic intrinsic_coordinate liftDifference_coordinate)
open CycleQ2HodgeEulerTangentDescent (quotientTangentIsoOfVertex)
open CycleQ2HodgeThreefoldTwist (homogeneousSection)
open CycleQ2FiniteCechDescent CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne
open CycleQ2HodgeEulerTangentToQuotient (values)
open CycleQ2InjectiveCech (AbSheaf)
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

abbrev T := Add ψ (tangent (toBase ψ))
def tangentProjection : F ⟶ T :=
  (SheafOfModules.toSheaf (threefold ψ).ringCatSheaf).map
    (cokernel.π (radialTangent ψ) ≫ (quotientTangentIsoOfVertex ψ vertex_unit).hom)

def representative (p : grade ψ 6) : One T (U ψ) := mapOne (U ψ) tangentProjection (cocycle p)

theorem representative_closed (p : grade ψ 6) : IsOneCocycle T (U ψ) (representative p) :=
  mapOne_closed (U ψ) tangentProjection (cocycle p) (closed p)

theorem representative_edge (p : grade ψ 6) (i j : Fin 4) (W : (threefold ψ).Opens)
    (hi : W ≤ U ψ i) (hj : W ≤ U ψ j) :
    edgeValue T (U ψ) (representative p) i j W hi hj =
      intrinsic ψ vertex_unit W (difference p i j W hi hj) := by
  unfold representative
  rw [edgeValue_mapOne, edge]
  rfl

def ksClass (p : grade ψ 6) : H ψ (tangent (toBase ψ)) 1 :=
  (connecting ψ smooth_parameter (homogeneousSection ψ p.val p.property ⊤)).comp
    (Ext.mk₀ tangentProjection) (Nat.add_zero 1)

theorem cechClass_eq_ks (p : grade ψ 6) :
    cechOneClass (U ψ) cover_eq_top (representative p) (representative_closed p) = ksClass p := by
  rw [show cechOneClass (U ψ) cover_eq_top (representative p) (representative_closed p) =
    (cechOneClass (U ψ) cover_eq_top (cocycle p) (closed p)).comp (Ext.mk₀ tangentProjection) _ from
      (cechOneClass_naturality (U ψ) cover_eq_top tangentProjection (cocycle p) (closed p)).symm,
    cechClass]
  rfl

theorem edge_coordinates (p : grade ψ 6) (i j : Fin 4) (W : (threefold ψ).Opens)
    (h : ∀ a : Fin 4, W ≤ U ψ a) (k : Fin 3) :
    let s := edgeValue T (U ψ) (representative p) i j W (h i) (h j)
    values ψ 0 W (h 0) s ((0 : Fin 5).succAbove ((0 : Fin 4).succAbove k)) =
      CycleQ2HodgeFermatYukawaRows.row W h i j p k := by
  dsimp only
  rw [representative_edge, intrinsic_coordinate]
  have hd (a : Fin 5) : CycleQ2HodgeEulerQuotientSections.rawCoordinate ψ 0 W (h 0) a
      (difference p i j W (h i) (h j)) =
      CycleQ2HodgeFermatYukawaRows.read W h j p a - CycleQ2HodgeFermatYukawaRows.read W h i p a :=
    liftDifference_coordinate ψ W 0 (h 0) _ _ ((lift_normal i W (h i) p.val p.property).trans
      (lift_normal j W (h j) p.val p.property).symm) a
  rw [hd, hd]
  rfl

end CycleQ2HodgeFermatTangentCochain
end
#print axioms CycleQ2HodgeFermatTangentCochain.cechClass_eq_ks
#print axioms CycleQ2HodgeFermatTangentCochain.edge_coordinates
