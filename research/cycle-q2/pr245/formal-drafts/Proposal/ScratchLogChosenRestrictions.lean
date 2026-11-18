import Proposal.ScratchWeightedProjectedSections
import Proposal.ScratchWeightedGradientSectionUnits
import Proposal.ScratchWeightedChosenResidue
import Proposal.GeometricConeVertexScalar

/-!
# The chosen vertex in the native section ring

The normalized coordinates of the gradient atlas agree with the dehomogenized
coordinates at the zeroth pivot. The map on the localized divisor identifies
the restriction of the normalized simple-pole coefficient with the regular
jet residue of the chosen section.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LogChosenRestrictions
open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2.Cech.Sections (algebra)
open CycleQ2GeometricAffineChartSections (chartSection chartSection_top)
open CycleQ2GeometricPrincipalChartSections (chartSection_compatible)
open CycleQ2GeometricHodgeThreefold (equation toBase coordinateOpen)
open CycleQ2HodgeEulerTangentAtlas (basicChart_inv_ι)
open CycleQ2HodgeEulerChartBinding (affineChart)
open CycleQ2HodgeEuler (chart chartMap dehom)
open CycleQ2WeightedResidueAtlas (U atlas affine Index inclusion)
open CycleQ2WeightedIntersectionFrame (Model)
open CycleQ2WeightedGenericPointMap (coordinateEquiv chosen)
open CycleQ2WeightedGradientSectionUnits (patch_le_coordinate eval_coordAt)
open CycleQ2WeightedNativeOverlapSection (coordAt chartAlg)
open CycleQ2WeightedConeUniversal (Base coefficients)
open CycleQ2WeightedChosenResidue (A V chartValue coneValue regularEval coefficient coordinate)
open CycleQ2WeightedProjectedSections (sectionEval sectionEval_coord)
open CycleQ2WeightedConeChartRestrictions (locality locality_map)
open CycleQ2ConeSimplexRings (Ambient quotient normal)
open CycleQ2WeightedCechPresentations (denominators)
open CycleQ2WeightedConeVertex (grad GradientRing coneNumerator residueSection)
open CycleQ2ConeSimplexNumerator (vCoeff)
open CycleQ2ConeVertexScalar (sectionTo sectionTo_polynomial normal_coordinate normalized_vertex)
open scoped CycleQ2WeightedConeUniversal

/-- Coordinate charts on an affine open, computed via its Spec equivalence. -/
private theorem top_preimage {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W)
    {S : Type} [CommRing S] (e : W.toScheme ≅ Spec (CommRingCat.of S)) (x : S) :
    chartSection e (Over.mk (𝟙 W)) x = Spec.preimage (hW.isoSpec.inv ≫ e.hom) x := by
  let f := hW.isoSpec.inv ≫ e.hom
  have h : CommRingCat.ofHom (chartSection e (Over.mk (𝟙 W))) = Spec.preimage f := by
    apply (cancel_mono (Scheme.ΓSpecIso Γ(X,W)).inv).mp
    rw [chartSection_top, Scheme.ΓSpecIso_inv_naturality (Spec.preimage f), Spec.map_preimage]
    simp only [f, Scheme.Hom.comp_appTop, hW.isoSpec_inv_appTop, Category.assoc]
  exact ConcreteCategory.congr_hom h x

theorem chartAlg_patch {k : Type} [CommRing k] (φ : CycleQ2GenericSexticGradient.CoeffRing →+* k)
    (a : Index) (p : chart φ a.1) :
    chartAlg φ a.1 (U φ a) (patch_le_coordinate φ a) p =
      coordinateEquiv φ a (algebraMap (chart φ a.1) (Model φ a) p) := by
  have h := chartSection_compatible (affineChart φ a.1) (atlas φ a) (patch_le_coordinate φ a)
    (algebraMap (chart φ a.1) (Model φ a))
    (basicChart_inv_ι (inclusion φ a.1) _) (Over.mk (𝟙 (U φ a))) p
  simp only [Category.id_comp] at h
  exact h.symm.trans (top_preimage (affine φ a) (atlas φ a) _)

local instance : Algebra Base A := algebra (toBase coefficients) V
local notation "P" => MvPolynomial (Fin 5) Base
local notation "G" => equation coefficients
local notation "W" => V
private abbrev hiPivot : W ≤ coordinateOpen coefficients (0 : Fin 4) :=
  patch_le_coordinate coefficients chosen
private abbrev x := coordAt coefficients 0 W hiPivot

theorem native_polynomial (p : P) : aeval x p = coneValue p :=
  (eval_coordAt coefficients 0 W hiPivot p).trans (chartAlg_patch coefficients chosen _)

theorem native_coordinate (j : Fin 5) : x j = coneValue (X j) := by
  simpa only [aeval_X] using native_polynomial (X j)

variable (T : Finset (Fin 5))
local notation "M" => denominators G (T : Set (Fin 5))
variable (hu : ∀ m : M, IsUnit (aeval x (m : P)))
abbrev read := sectionEval coefficients M 0 W hiPivot hu

theorem read_polynomial (p : P) :
    read T hu (quotient G T (algebraMap P (Ambient G T) p)) = coneValue p := by
  change locality M x hu (algebraMap P (Ambient G T) p) = coneValue p
  rw [locality_map, native_polynomial]

theorem read_pivot :
    read T hu (CycleQ2WeightedConeChartRestrictions.coord coefficients M 0) = 1 := by
  rw [read, sectionEval_coord, native_coordinate]
  change chartValue (dehom (0 : Fin 4) (X ((0 : Fin 4).castSucc))) = 1
  rw [CycleQ2HodgeEuler.dehom_X_self, map_one]

theorem read_spatial (j : Fin 3) :
    read T hu (CycleQ2WeightedConeChartRestrictions.coord coefficients M j.succ.succ) = coordinate j := by
  rw [read, sectionEval_coord, native_coordinate]
  change chartValue (dehom (0 : Fin 4) (X j.succ.succ)) = chartValue (X j.succ)
  apply congrArg chartValue
  simpa only [Fin.zero_succAbove] using CycleQ2HodgeEuler.dehom_X_succAbove (R := Base) 0 j.succ

variable (h : (1 : Fin 5) ∈ T)
theorem read_away (z : GradientRing 1 G) :
    read T hu (quotient G T (sectionTo G T 1 h z)) = regularEval z := by
  have he : ((read T hu).toRingHom.comp (quotient G T).toRingHom).comp (sectionTo G T 1 h) =
      regularEval := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (grad 1 G))
    ext1 p
    change read T hu (quotient G T (sectionTo G T 1 h (algebraMap P (GradientRing 1 G) p))) =
      regularEval (algebraMap P (GradientRing 1 G) p)
    rw [sectionTo_polynomial, read_polynomial]
    exact (IsLocalization.Away.lift_eq _ _ _).symm
  exact RingHom.congr_fun he z

variable (hT : ∀ i ∈ T, pderiv i G ≠ 0)
/-- Restricting the chosen vertex's normal residue through the actual cone divisor
produces the regular coefficient used in the literal generic-point computation. -/
theorem read_coefficient :
    read T hu (quotient G T (vCoeff coefficients T hT 1 h * normal G h (CycleQ2ConeSimplexRings.coord G T 1))) = coefficient := by
  change _ = regularEval (residueSection 1 G (coneNumerator Base))
  rw [normal_coordinate, normalized_vertex, read_away]

end CycleQ2LogChosenRestrictions
end
#print axioms CycleQ2LogChosenRestrictions.read_pivot
#print axioms CycleQ2LogChosenRestrictions.read_spatial
#print axioms CycleQ2LogChosenRestrictions.read_coefficient
