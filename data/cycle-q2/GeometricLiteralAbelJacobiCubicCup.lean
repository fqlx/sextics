import Proposal.GeometricIncidenceFirstOrderCanonicalH2
import Proposal.GeometricLiteralCotangentTrace
import Proposal.GeometricFiniteCechTwoNaturality

/-!
# The canonical-valued cup on the original twelve-open atlas

The retained cubic sends the actual sheaf-valued tangent and Chern
contraction to the canonical sheaf of the original projective surface.
The sign of the Cartier connecting morphism gives its nonvanishing.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiCubicCup

open CategoryTheory TopologicalSpace AlgebraicGeometry
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2CanonicalCubicDiagram
  CycleQ2CanonicalResidueDiagram CycleQ2CanonicalResidueSheaf
  CycleQ2LiteralSheafChernKodairaSpencerCup CycleQ2LiteralCartierProjectedCup
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeCupDerivedClass CycleQ2GlobalSurfaceCubics

local instance surfaceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology
      (show TopCat from CycleQ2CanonicalResidueSheaf.Surface)) AddCommGrpCat.{0}) := HasExt.standard _

attribute [local instance] CycleQ2CanonicalResidueDiagram.canonicalSectionModule

abbrev canonicalCupMap : coefficientSheaf ⟶ canonicalResidueAdditiveComplex.X₁ :=
  (globalFormAdditiveDiagram (globalCubicSection firstOrderWeightedCubic)).τ₁

def canonicalCupCocycle : Two canonicalResidueAdditiveComplex.X₁ cover :=
  mapTwo cover canonicalCupMap sheafCupCocycle

theorem canonicalCup_normalized :
    NormalizedTwo canonicalResidueAdditiveComplex.X₁ cover canonicalCupCocycle :=
  mapTwo_normalized cover canonicalCupMap sheafCupCocycle sheafCupCocycle_normalized

theorem canonicalCup_closed :
    IsTwoCocycle canonicalResidueAdditiveComplex.X₁ cover canonicalCupCocycle :=
  mapTwo_closed cover canonicalCupMap sheafCupCocycle sheafCupCocycle_closed

/-- On every ordered face of the original cover, the canonical coefficient is the
restriction of the global cubic two-form times the original sheaf cup value. -/
theorem canonicalCup_face_increasing (u v w : Vertex) (huv : rank u < rank v) (hvw : rank v < rank w)
    (W : CycleQ2CanonicalResidueSheaf.Surface.Opens) (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    faceValue canonicalResidueAdditiveComplex.X₁ cover canonicalCupCocycle u v w W hu hv hw =
      (show Γ(CycleQ2CanonicalResidueSheaf.Surface,W) from sheafCupValue u v w W hu hv hw) •
        formRestriction (globalCubicSection firstOrderWeightedCubic) W := by
  unfold canonicalCupCocycle
  rw [faceValue_mapTwo, sheafCupCocycle_eq_native, nativeCupCocycle_eq_gaugeAdjusted,
    gaugeAdjustedCup_increasing u v w huv hvw W hu hv hw, sheafCupValue_eq_native]
  rfl

theorem cubicH2_sheafCup_ne_zero :
    cubicH2 firstOrderWeightedCubic sheafCupDerivedClass ≠ 0 := by
  rw [sheafCupDerivedClass_eq_original, projectedDerivedClass_eq_negative_original, map_neg, neg_ne_zero]
  exact firstOrder_canonicalH2_ne_zero

def canonicalCupClass : canonicalResidueAdditiveComplex.X₁.H' 2 ⊤ :=
  cechTwoClass cover cover_covers canonicalCupCocycle canonicalCup_normalized canonicalCup_closed

theorem canonicalCupClass_eq :
    canonicalCupClass = cubicH2 firstOrderWeightedCubic sheafCupDerivedClass := by
  let h := CycleQ2FiniteCechTwoNaturality.cechTwoClass_naturality
    (X := (show TopCat from CycleQ2CanonicalResidueSheaf.Surface)) (ι := Vertex)
    (F := coefficientSheaf) (G := canonicalResidueAdditiveComplex.X₁)
    cover cover_covers canonicalCupMap sheafCupCocycle sheafCupCocycle_normalized sheafCupCocycle_closed
  exact h.symm

theorem canonicalCupClass_ne_zero : canonicalCupClass ≠ 0 := by
  rw [canonicalCupClass_eq]
  exact cubicH2_sheafCup_ne_zero

/-- The fixed top Laurent coefficient detects the original twelve-open cup. -/
theorem canonicalCupClass_trace_ne_zero :
    CycleQ2LiteralCotangentTrace.algebraicTrace canonicalCupClass ≠ 0 :=
  fun h => canonicalCupClass_ne_zero ((CycleQ2LiteralCotangentTrace.algebraicTrace_eq_zero_iff _).mp h)

theorem canonicalCupClass_sectionTrace (s : CycleQ2LiteralCotangentTrace.TripleSections)
    (hs : CycleQ2CanonicalCoordinateH2.canonicalConnecting s = canonicalCupClass) :
    CycleQ2CanonicalResidueNonzero.canonicalSectionTrace s =
      CycleQ2LiteralCotangentTrace.algebraicTrace canonicalCupClass := by
  rw [← hs, CycleQ2LiteralCotangentTrace.algebraicTrace_eq]

end CycleQ2LiteralAbelJacobiCubicCup

end

#print axioms CycleQ2LiteralAbelJacobiCubicCup.canonicalCup_face_increasing
#print axioms CycleQ2LiteralAbelJacobiCubicCup.cubicH2_sheafCup_ne_zero

#print axioms CycleQ2LiteralAbelJacobiCubicCup.canonicalCupClass_ne_zero
#print axioms CycleQ2LiteralAbelJacobiCubicCup.canonicalCupClass_trace_ne_zero
