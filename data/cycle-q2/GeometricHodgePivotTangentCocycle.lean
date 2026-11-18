import Proposal.GeometricHodgePivotNormalLifts
import Proposal.GeometricHodgeNormalConnectingCech
import Proposal.GeometricHodgeEulerTangentRepresentatives

/-!
# Projective Kodaira–Spencer cocycles on the four moving pivot opens

The classes obtained from ordinary degree-six normal sections are represented
on D₊(xᵢFᵢ) by differences of the explicit native lifts. On the common
intersection their evaluations on the three free coordinates are the rows
of the four-dimensional homogeneous gradient calculation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgePivotTangentCocycle

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace CategoryTheory.Abelian
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeEulerSheaf CycleQ2HodgeNormalCohomology
open CycleQ2HodgeEulerTangentRepresentatives (intrinsic intrinsic_coordinate)
open CycleQ2HodgeEulerTangentDescent (quotientTangentIsoOfVertex)
open CycleQ2HodgeEulerQuotientFrames (euler)
open CycleQ2HodgeEulerQuotientSections (rawCoordinate)
open CycleQ2HodgeEulerTangentToQuotient (values)
open CycleQ2HodgeEulerTangentSheaf (tangent)
open CycleQ2HodgeTwistGradientCover (pivotOpen)
open CycleQ2HodgePivotNormalLifts (sourceChart)
open CycleQ2SeedSectionSheafLocal (moduleRes)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2FiniteCechDescent CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne
open CycleQ2InjectiveCech (AbSheaf)
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))

private theorem factors : IsUnit (φ CycleQ2GenericSexticGradient.gradientOpen) ∧ IsUnit (φ vertexCoefficient) := by
  simpa only [goodParameter, map_mul, IsUnit.mul_iff] using hg

theorem cover : (⨆ i, pivotOpen φ i) = ⊤ := CycleQ2HodgeTwistGradientCover.cover φ (factors φ hg).1

abbrev K := Add φ (rawTangent φ)
abbrev T := Add φ (tangent (toBase φ))
abbrev normalSection (p : grade φ 6) := homogeneousSection φ p.val p.property ⊤
abbrev lifts (p : grade φ 6) (i : Fin 4) := CycleQ2HodgePivotNormalLifts.lift φ i (pivotOpen φ i) le_rfl p

private theorem lifts_over (p : grade φ 6) (i : Fin 4) :
    (normalMap φ).app (pivotOpen φ i) (lifts φ p i) = moduleRes (twist φ 6) le_top (normalSection φ p) := by
  change (normalMap φ).app _ (CycleQ2HodgePivotNormalLifts.lift φ i _ _ _) =
    moduleRes (twist φ 6) le_top (homogeneousSection φ p.val p.property ⊤)
  rw [CycleQ2HodgePivotNormalLifts.lift_normal, homogeneousSection_restrict]

abbrev normalCocycle (p : grade φ 6) : One (K φ) (pivotOpen φ) :=
  CycleQ2HodgeNormalConnectingCech.cocycle φ (pivotOpen φ) (normalSection φ p) (lifts φ p) (lifts_over φ p)

abbrev normalClosed (p : grade φ 6) : IsOneCocycle (K φ) (pivotOpen φ) (normalCocycle φ p) :=
  CycleQ2HodgeNormalConnectingCech.closed φ (pivotOpen φ) (normalSection φ p) (lifts φ p) (lifts_over φ p)

def projection : K φ ⟶ T φ :=
  (SheafOfModules.toSheaf (threefold φ).ringCatSheaf).map
    (cokernel.π (radialTangent φ) ≫ (quotientTangentIsoOfVertex φ (factors φ hg).2).hom)

def representative (p : grade φ 6) : One (T φ) (pivotOpen φ) :=
  mapOne (pivotOpen φ) (projection φ hg) (normalCocycle φ p)

theorem closed (p : grade φ 6) : IsOneCocycle (T φ) (pivotOpen φ) (representative φ hg p) :=
  mapOne_closed (pivotOpen φ) (projection φ hg) (normalCocycle φ p) (normalClosed φ p)

def ksClass (p : grade φ 6) : H φ (tangent (toBase φ)) 1 :=
  (connecting φ hg (normalSection φ p)).comp (Ext.mk₀ (projection φ hg)) (Nat.add_zero 1)

theorem cechClass (p : grade φ 6) :
    cechOneClass (pivotOpen φ) (cover φ hg) (representative φ hg p) (closed φ hg p) = ksClass φ hg p := by
  have h := cechOneClass_naturality (pivotOpen φ) (cover φ hg) (projection φ hg)
    (normalCocycle φ p) (normalClosed φ p)
  refine h.symm.trans ?_
  rw [show cechOneClass (pivotOpen φ) (cover φ hg) (normalCocycle φ p) (normalClosed φ p) = _ from
    CycleQ2HodgeNormalConnectingCech.cechClass φ (pivotOpen φ) (normalSection φ p) (lifts φ p)
      (lifts_over φ p) hg (cover φ hg)]
  rfl

variable (V : (threefold φ).Opens) (h : ∀ i : Fin 4, V ≤ pivotOpen φ i)
abbrev h₀ := sourceChart φ 0 V (h 0)
abbrev d (i : Fin 4) := CycleQ2HodgePivotNormalLifts.inverse φ i V (h i) 0 (h₀ φ V h)
abbrev radial := euler φ 0 V (h₀ φ V h)
abbrev value (p : grade φ 6) := normalized φ 0 p.val p.property V (h₀ φ V h)
abbrev tangentEdge (p : grade φ 6) (i j : Fin 4) :=
  edgeValue (T φ) (pivotOpen φ) (representative φ hg p) i j V (h i) (h j)

theorem edge_coordinates (p : grade φ 6) (i j : Fin 4) (k : Fin 3) :
    values φ 0 V (h₀ φ V h) (tangentEdge φ hg V h p i j) ((0 : Fin 5).succAbove ((0 : Fin 4).succAbove k)) =
      CycleQ2HodgeFermatYukawaDeterminant.row (radial φ V h) (d φ V h) i j (value φ V h p) k := by
  let n := CycleQ2HodgeNormalConnectingCech.difference φ (pivotOpen φ) (normalSection φ p) (lifts φ p)
    (lifts_over φ p) i j V (h i) (h j)
  have hn : (kernel.ι (normalMap φ)).app V n =
      CycleQ2HodgePivotNormalLifts.lift φ j V (h j) p - CycleQ2HodgePivotNormalLifts.lift φ i V (h i) p := by
    rw [show (kernel.ι (normalMap φ)).app V n = _ from
      CycleQ2HodgeNormalConnectingCech.difference_val φ (pivotOpen φ) (normalSection φ p) (lifts φ p)
        (lifts_over φ p) i j V (h i) (h j)]
    change moduleRes (raw φ) _ (CycleQ2HodgePivotNormalLifts.lift φ j _ _ _) -
      moduleRes (raw φ) _ (CycleQ2HodgePivotNormalLifts.lift φ i _ _ _) = _
    rw [CycleQ2HodgePivotNormalLifts.lift_restrict, CycleQ2HodgePivotNormalLifts.lift_restrict]
  have he : tangentEdge φ hg V h p i j = intrinsic φ (factors φ hg).2 V n := by
    unfold tangentEdge representative
    rw [edgeValue_mapOne, normalCocycle, CycleQ2HodgeNormalConnectingCech.edge]
    rfl
  let l := CycleQ2HodgeFermatYukawaDeterminant.lift (d φ V h)
  have hr (a : Fin 5) : rawCoordinate φ 0 V (h₀ φ V h) a n =
      l j (value φ V h p) a - l i (value φ V h p) a := by
    change chartFrame φ _ 0 V _ ((Pi.π (pieces φ) a).app V ((kernel.ι (normalMap φ)).app V n)) = _
    rw [hn, map_sub, map_sub]
    exact congrArg₂ (· - ·)
      (congrFun (CycleQ2HodgePivotNormalLifts.read_lift φ j V (h j) p h) a)
      (congrFun (CycleQ2HodgePivotNormalLifts.read_lift φ i V (h i) p h) a)
  rw [he, intrinsic_coordinate, hr, hr]
  change (_ - _) - (_ - _) * _ = (_ - _ * _) - (_ - _ * _)
  ring

end CycleQ2HodgePivotTangentCocycle
end
#print axioms CycleQ2HodgePivotTangentCocycle.cechClass
#print axioms CycleQ2HodgePivotTangentCocycle.edge_coordinates
