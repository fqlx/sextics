import Proposal.GeometricClosedEmbeddingCohomology
import Proposal.GeometricLiteralThreefoldCanonicalFrame
import Proposal.GeometricLiteralThreefoldHodgeCech
import Proposal.GeometricHodgeThreefoldLiteral
import Proposal.GeometricHodgeDerivedTopTrace
import Proposal.GeometricHodgeTwistTorusChart

/-!
# Top cohomology and its normalized Laurent trace on the fixed threefold

The four-open comparison identifies every degree-three class of the
structure sheaf with a Laurent section modulo the signed face restrictions.
The single surviving coefficient gives the trace. Transport by the literal
incidence isomorphism and multiplication by the canonical residue volume
give the corresponding trace on three-forms of the marked smooth threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldTopTrace

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf additiveForget)
open CycleQ2ClosedEmbeddingSheafExact (push)
open CycleQ2ClosedEmbeddingCohomology (pushHEquiv)
open CycleQ2InjectiveCech (AbSheaf)

local instance (X : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _

variable {X Y : Scheme.{0}} (e : X ≅ Y)

def structurePushIso : structureAdditiveSheaf Y ≅
    (push e.hom.base).obj (structureAdditiveSheaf X) := by
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun U => additiveForget.mapIso (asIso (e.hom.app U.unop))) ?_
  intro U V f
  change additiveForget.map (Y.presheaf.map f) ≫ additiveForget.map (e.hom.app V.unop) =
    additiveForget.map (e.hom.app U.unop) ≫ additiveForget.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg additiveForget.map (e.hom.naturality f)

def structureCohomology (n : ℕ) :
    (structureAdditiveSheaf X).H' n ⊤ ≃+ (structureAdditiveSheaf Y).H' n ⊤ :=
  (pushHEquiv e.hom.base e.hom.isClosedEmbedding (structureAdditiveSheaf X) n).trans
    ((((Sheaf.cohomologyPresheafFunctor _ n).mapIso (structurePushIso e).symm).app (op ⊤)).addCommGroupIsoToAddEquiv)

open CycleQ2LiteralThreefoldCanonicalFrame (volumeIso)
open CycleQ2LiteralThreefoldCanonicalVolume (threeForms)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2LiteralThreefoldHodgeCech (Threefold)

def canonicalCohomology (n : ℕ) :
    (structureAdditiveSheaf Threefold).H' n ⊤ ≃+ (addSheaf threeForms).H' n ⊤ := by
  let e := (SheafOfModules.toSheaf Threefold.ringCatSheaf).mapIso volumeIso
  exact (((Sheaf.cohomologyPresheafFunctor _ n).mapIso e).app (op ⊤)).addCommGroupIsoToAddEquiv

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold vertexCoefficient)
open CycleQ2GeometricHodgeThreefoldIncidence (literalEval literalIso literal_vertex_unit)
open CycleQ2HodgeTwistTorusChart (structureLaurentSections)
open CycleQ2HodgeFourOpenStructureHThree (TopSection tripleConnecting)
open CycleQ2HodgeDerivedTopTrace (derivedTrace derivedTrace_connecting topCoordinates representative)

variable {R : Type} [CommRing R] [Nontrivial R] (φ : CoeffRing →+* R) (h : IsUnit (φ vertexCoefficient))

/-- The trace on all of H³ of the structure sheaf on the actual monic sextic. -/
def structureTrace : (structureAdditiveSheaf (threefold φ)).H' 3 ⊤ ≃+ R :=
  derivedTrace φ h (structureLaurentSections φ h)

theorem structureTrace_connecting (p : TopSection φ) :
    structureTrace φ h (tripleConnecting φ h p) =
      CycleQ2HodgeTopCech.trace (topCoordinates (structureLaurentSections φ h) p) :=
  derivedTrace_connecting φ h _ p

/-- Change from the universal-family seed model to the fixed threefold, followed
by multiplication by its global Kähler volume form. -/
def toCanonical :
    (structureAdditiveSheaf (threefold literalEval)).H' 3 ⊤ ≃+ (addSheaf threeForms).H' 3 ⊤ :=
  (structureCohomology literalIso 3).trans (canonicalCohomology 3)

/-- Normalized additive trace on the genuine canonical cohomology of the marked threefold. -/
def canonicalTrace : (addSheaf threeForms).H' 3 ⊤ ≃+ ℂ :=
  toCanonical.symm.trans (structureTrace literalEval literal_vertex_unit)

theorem canonicalTrace_connecting (p : TopSection literalEval) :
    canonicalTrace (toCanonical (tripleConnecting literalEval literal_vertex_unit p)) =
      CycleQ2HodgeTopCech.trace (topCoordinates (structureLaurentSections literalEval literal_vertex_unit) p) := by
  simp only [canonicalTrace, AddEquiv.trans_apply, AddEquiv.symm_apply_apply, structureTrace_connecting]

/-- A representative of each prescribed trace is the corresponding multiple of
the square of the weight-two coordinate divided by the four weight-one coordinates. -/
theorem canonicalTrace_representative (a : ℂ) :
    canonicalTrace (toCanonical (tripleConnecting literalEval literal_vertex_unit
      (representative (structureLaurentSections literalEval literal_vertex_unit) a))) = a := by
  rw [canonicalTrace_connecting]
  exact CycleQ2HodgeDerivedTopTrace.sectionTrace_representative _ a

end CycleQ2LiteralThreefoldTopTrace

#print axioms CycleQ2LiteralThreefoldTopTrace.structureTrace
#print axioms CycleQ2LiteralThreefoldTopTrace.canonicalTrace_representative
