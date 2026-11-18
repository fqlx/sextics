import Proposal.GeometricLiteralTimeCurveCompletion
import Proposal.GeometricLiteralAbelJacobiTimeFamily

/-!
# The marked connected component of the proper time base

On a Noetherian space each connected component is clopen. The component of
the original complex seed therefore gives a proper connected scheme. Both
the marked point and its original nonconstant dual-number motion factor
through this component.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeSeedComponent

open AlgebraicGeometry CategoryTheory Set TopologicalSpace
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralTimeCurveCompletion
  CycleQ2LiteralIncidenceTimeCurve CycleQ2IncidenceFirstOrder CycleQ2FirstOrderNeighborhood
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

/-- The complement of a connected component is the finite union of the
irreducible components disjoint from it. -/
theorem isOpen_component_of_noetherian {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (x : X) : IsOpen (connectedComponent x) := by
  let D := {Z ∈ irreducibleComponents X | Disjoint Z (connectedComponent x)}
  have hfin : D.Finite := NoetherianSpace.finite_irreducibleComponents.subset (fun _ h => h.1)
  have heq : (connectedComponent x)ᶜ = ⋃₀ D := by
    ext y
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      apply Set.disjoint_left.mpr
      intro z hz hzc
      apply hy
      rw [connectedComponent_eq hzc]
      exact isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent hz
        mem_irreducibleComponent
    · rintro ⟨Z, hZ, hy⟩ hx
      exact Set.disjoint_left.mp hZ.2 hy hx
  apply isClosed_compl_iff.mp
  rw [heq, Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

abbrev Base := Completion (timeOpen V)

/-- The projective closure is of finite type over the complex point. -/
instance baseNoetherian : IsNoetherian (Base V) := by
  have := QuasiCompact.compactSpace_of_compactSpace (structureMap (timeOpen V))
  exact { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (structureMap (timeOpen V)) }

def markedPoint : Base V :=
  (seedLift V hV ≫ inclusion (timeOpen V)) (default : Spec (CommRingCat.of ℂ))

def componentOpen : (Base V).Opens :=
  ⟨connectedComponent (markedPoint V hV), isOpen_component_of_noetherian _⟩

abbrev Component := (componentOpen V hV).toScheme

instance componentConnected : ConnectedSpace (Component V hV) :=
  Subtype.connectedSpace (isConnected_connectedComponent (x := markedPoint V hV))

theorem component_clopen : IsClopen (componentOpen V hV : Set (Base V)) :=
  ⟨isClosed_connectedComponent, (componentOpen V hV).isOpen⟩

instance componentClosedImmersion : IsClosedImmersion (componentOpen V hV).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact (component_clopen V hV).1

abbrev componentStructure := (componentOpen V hV).ι ≫ structureMap (timeOpen V)

instance componentProper : IsProper (componentStructure V hV) :=
  inferInstanceAs (IsProper ((componentOpen V hV).ι ≫ structureMap (timeOpen V)))

/-- The original marked point, valued in its component. -/
def componentSeed : Spec (CommRingCat.of ℂ) ⟶ Component V hV :=
  IsOpenImmersion.lift (componentOpen V hV).ι (seedLift V hV ≫ inclusion (timeOpen V)) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim z default]
    exact mem_connectedComponent)

@[reassoc (attr := simp)] theorem componentSeed_fac :
    componentSeed V hV ≫ (componentOpen V hV).ι = seedLift V hV ≫ inclusion (timeOpen V) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The full dual-number morphism factors through the same component. -/
def componentTangent : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ Component V hV :=
  IsOpenImmersion.lift (componentOpen V hV).ι (tangentLift V hV ≫ inclusion (timeOpen V)) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, firstOrderPoint_eq_closedPoint z]
    change ((firstOrderClosedPoint ≫ tangentLift V hV) ≫ inclusion (timeOpen V))
      (default : Spec (CommRingCat.of ℂ)) ∈ componentOpen V hV
    rw [tangentLift_at_seed]
    exact mem_connectedComponent)

@[reassoc (attr := simp)] theorem componentTangent_fac :
    componentTangent V hV ≫ (componentOpen V hV).ι = tangentLift V hV ≫ inclusion (timeOpen V) :=
  IsOpenImmersion.lift_fac _ _ _

theorem componentTangent_at_seed : firstOrderClosedPoint ≫ componentTangent V hV =
    componentSeed V hV := by
  apply (cancel_mono (componentOpen V hV).ι).mp
  rw [Category.assoc, componentTangent_fac, componentSeed_fac, ← Category.assoc, tangentLift_at_seed]

@[reassoc (attr := simp)] theorem componentSeed_over :
    componentSeed V hV ≫ componentStructure V hV = 𝟙 _ := by
  rw [componentStructure, ← Category.assoc, componentSeed_fac, Category.assoc, inclusion_over,
    ← Category.assoc, seedLift_fac]
  exact CategoryTheory.Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem componentTangent_over :
    componentTangent V hV ≫ componentStructure V hV = structureDual := by
  rw [componentStructure, ← Category.assoc, componentTangent_fac, Category.assoc, inclusion_over,
    ← Category.assoc, tangentLift_fac]
  exact CategoryTheory.Limits.pullback.lift_fst _ _ _

theorem componentReduced [AlgebraicGeometry.IsReduced (Base V)] :
    AlgebraicGeometry.IsReduced (Component V hV) :=
  isReduced_of_isOpenImmersion (componentOpen V hV).ι

theorem componentTangent_nonconstant :
    componentTangent V hV ≠ structureDual ≫ componentSeed V hV := by
  intro he
  apply tangentLift_nonconstant V hV
  apply (cancel_mono (inclusion (timeOpen V))).mp
  simpa only [Category.assoc, componentSeed_fac, componentTangent_fac] using
    congrArg (fun f => f ≫ (componentOpen V hV).ι) he

#print axioms componentConnected
#print axioms componentProper
#print axioms componentTangent_at_seed
#print axioms componentTangent_nonconstant

end CycleQ2LiteralTimeSeedComponent
end
