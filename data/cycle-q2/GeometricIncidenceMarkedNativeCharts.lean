import Proposal.GeometricIncidenceMarkedProjectorCharts
import Proposal.GeometricProjectorUnitDefect
import Proposal.GeometricLiteralMovingDivisorCoordinate
import Proposal.GeometricLiteralMovingPivotPrincipal

/-!
# Native degree-zero frames in the refined marked cone

A principal localization of a native chart maps into the localized cone
as soon as its reduced denominator is invertible. This includes any lift
of a dehomogenized pivot product. The map respects reduction and the
square-zero coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IncidenceMarkedNativeCharts

open HomogeneousLocalization CycleQ2GeometricProjectorDefect CycleQ2GeometricKernelLocalization
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralIntersectionEpsilonTransport
  CycleQ2IncidenceMarkedProjectorCharts CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedDeformationEquiv

attribute [local instance] CycleQ2LiteralIntersectionEpsilonTransport.ordinaryReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra

variable (t : Finset Vertex) (q : ThickCone t) (p : ThickRing t)

def thickBase : ThickRing t →+* RefinedThick t q :=
  (algebraMap (ThickCone t) _).comp (algebraMap (ThickRing t) (ThickCone t))

def closedBase : ClosedRing t →+* RefinedClosed t q :=
  (algebraMap (ClosedCone t) _).comp (algebraMap (ClosedRing t) (ClosedCone t))

theorem reduction_base (z : ThickRing t) :
    refinedReduction t q (thickBase t q z) = closedBase t q (nativeReduction t z) :=
  (refinedReduction_base t q z.val).trans (congrArg (algebraMap (ClosedCone t) (RefinedClosed t q))
    (ordinaryReduction_val t z))

/-- A homogeneous polynomial that is invertible on the refined cone
also gives an invertible reduced degree-zero entry in every coordinate frame. -/
theorem normalized_reduced_unit (v : Vertex) (hv : v ∈ t) {d : ℕ} (g : GradedDeformation)
    (hg : g ∈ deformationGrade d)
    (hu : IsUnit (algebraMap (ThickCone t) (RefinedThick t q)
      (algebraMap GradedDeformation (ThickCone t) g))) :
    IsUnit (closedBase t q (nativeReduction t (normalized t v hv g hg))) := by
  rw [← reduction_base t q]
  apply IsUnit.map
  apply isUnit_of_mul_isUnit_left (y := algebraMap (ThickCone t) (RefinedThick t q) (coordinateValue t v ^ d))
  change IsUnit (algebraMap (ThickCone t) (RefinedThick t q) (normalized t v hv g hg).val * _)
  rw [← map_mul, normalized_val_mul]
  exact hu

abbrev PivotVertex := Vertex × (Fin 3 × Fin 3)

def seedPivot (a : PivotVertex) : CycleQ2SeedTrace.WeightedPoly :=
  CycleQ2IncidenceEquations.rawSeedMatrix (57 : ℂ) a.2.1 a.2.2

theorem seedPivot_homogeneous (a : PivotVertex) :
    (seedPivot a).IsWeightedHomogeneous CycleQ2GeometricCoordinateWeight.weight 14 :=
  CycleQ2GeometricIncidenceProj.homogeneous_of_character
    (CycleQ2IncidenceEquations.rawSeedMatrix_homogeneous (57 : ℂ) a.2.1 a.2.2)

/-- The degree-zero lift of the seed matrix pivot is the specified moving
matrix entry as an actual regular function on the projective intersection. -/
theorem seedPivotSection (hs : t.Nonempty) (a : PivotVertex) (hv : a.1 ∈ t) :
    CycleQ2LiteralProjectiveIntersectionRestrictions.closedSectionsEquiv t hs
      (nativeReduction t (normalized t a.1 hv (polynomialInGraded (seedPivot a))
        (polynomialPivot_homogeneous (seedPivot_homogeneous a)))) =
      CycleQ2SeedProjectiveImageCocycle.sectionMatrix a.1.2 (closedOpen t)
        (CycleQ2LiteralMovingDivisorCoordinate.closedOpen_le_patch t a.1 hv) a.2.1 a.2.2 := by
  rw [CycleQ2SeedProjectiveImageCocycle.sectionMatrix_entry]
  exact CycleQ2LiteralMovingDivisorCoordinate.normalized_polynomialSection t hs a.1 hv 14 _
    (polynomialPivot_homogeneous (seedPivot_homogeneous a)) _ (seedPivot_homogeneous a)
    (CycleQ2LiteralGradedReduction.reduction_polynomial _)

/-- Every original seed matrix pivot selected for the intersection becomes
an invertible regular function in its own native coordinate frame. -/
theorem seedPivotUnit (S : Finset PivotVertex) (a : PivotVertex) (ha : a ∈ S) (hv : a.1 ∈ t) :
    IsUnit (closedBase t (pivotProduct t seedPivot S)
      (nativeReduction t (normalized t a.1 hv (polynomialInGraded (seedPivot a))
        (polynomialPivot_homogeneous (seedPivot_homogeneous a))))) :=
  normalized_reduced_unit t (pivotProduct t seedPivot S) a.1 hv
    (polynomialInGraded (seedPivot a)) (polynomialPivot_homogeneous (seedPivot_homogeneous a))
    (polynomialPivot_isUnit t seedPivot S a ha)

theorem pivotEntry_eq_normalized (hs : t.Nonempty) (a : PivotVertex) (hv : a.1 ∈ t) :
    CycleQ2LiteralMovingPivotPrincipal.pivotEntry t hs a hv =
      nativeReduction t (normalized t a.1 hv (polynomialInGraded (seedPivot a))
        (polynomialPivot_homogeneous (seedPivot_homogeneous a))) := by
  apply (CycleQ2LiteralProjectiveIntersectionRestrictions.closedSectionsEquiv t hs).injective
  exact (CycleQ2LiteralMovingPivotPrincipal.pivotEntry_section t hs a hv).trans
    (seedPivotSection t hs a hv).symm

def tripleDenominator (a b c : PivotVertex) : ThickCone (CycleQ2LiteralMovingPivotPrincipal.vertices a b c) :=
  pivotProduct (CycleQ2LiteralMovingPivotPrincipal.vertices a b c) seedPivot {a,b,c}

/-- The actual product defining the native triple pivot face becomes a unit
in the single cone localization at the product of the raw matrix entries. -/
theorem nativeTripleProduct_isUnit (a b c : PivotVertex) :
    IsUnit (closedBase _ (tripleDenominator a b c)
      (CycleQ2LiteralMovingPivotPrincipal.pivotProduct a b c)) := by
  let S : Finset PivotVertex := {a,b,c}
  let T := CycleQ2LiteralMovingPivotPrincipal.vertices a b c
  have hu (z : PivotVertex) (hz : z ∈ S) (hv : z.1 ∈ T) :
      IsUnit (closedBase T (tripleDenominator a b c)
        (CycleQ2LiteralMovingPivotPrincipal.pivotEntry T (CycleQ2LiteralMovingPivotPrincipal.inhabitedVertices a b c) z hv)) := by
    rw [pivotEntry_eq_normalized]
    exact seedPivotUnit T S z hz hv
  simp only [CycleQ2LiteralMovingPivotPrincipal.pivotProduct, map_mul]
  exact ((hu a (by simp [S]) (by simp [T,CycleQ2LiteralMovingPivotPrincipal.vertices])).mul
    (hu b (by simp [S]) (by simp [T,CycleQ2LiteralMovingPivotPrincipal.vertices]))).mul
      (hu c (by simp [S]) (by simp [T,CycleQ2LiteralMovingPivotPrincipal.vertices]))

variable (hq : IsUnit (closedBase t q (nativeReduction t p)))

private theorem thick_unit : IsUnit (thickBase t q p) := by
  apply CycleQ2ProjectorUnitDefect.isUnit_of_reduced_unit (refinedReduction t q)
    (refinedCoefficients t q) (localReduction_surjective (ThickCone t) (ClosedCone t)
      (CycleQ2LiteralProjectiveIntersectionSplittings.ordinaryReduction_surjective t) q)
  rw [reduction_base]
  exact hq

def nativeThickMap : ThickAt (ThickRing t) p →+* RefinedThick t q :=
  IsLocalization.Away.lift p (g := thickBase t q) (thick_unit t q p hq)

def nativeClosedMap : ClosedAt (ThickRing t) (ClosedRing t) p →+* RefinedClosed t q :=
  IsLocalization.Away.lift (nativeReduction t p) (g := closedBase t q) hq

theorem nativeThickMap_base (z : ThickRing t) :
    nativeThickMap t q p hq (algebraMap _ _ z) = thickBase t q z :=
  IsLocalization.Away.lift_eq p (thick_unit t q p hq) z

theorem nativeClosedMap_base (z : ClosedRing t) :
    nativeClosedMap t q p hq (algebraMap _ _ z) = closedBase t q z :=
  IsLocalization.Away.lift_eq (nativeReduction t p) hq z

theorem nativeThickMap_reduction (z : ThickAt (ThickRing t) p) :
    refinedReduction t q (nativeThickMap t q p hq z) =
      nativeClosedMap t q p hq (localReduction (ThickRing t) (ClosedRing t) p z) := by
  have he : (refinedReduction t q).comp (nativeThickMap t q p hq) =
      (nativeClosedMap t q p hq).comp (localReduction (ThickRing t) (ClosedRing t) p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers p)
    apply RingHom.ext
    intro b
    exact (congrArg (refinedReduction t q) (nativeThickMap_base t q p hq b)).trans
      ((reduction_base t q b).trans ((nativeClosedMap_base t q p hq (nativeReduction t b)).symm.trans
        (congrArg (nativeClosedMap t q p hq) (localReduction_base (ThickRing t) (ClosedRing t) p b).symm)))
  exact RingHom.congr_fun he z

private theorem epsilon_val (z : ClosedRing t) :
    (epsilonCoefficient t z).val = ordinaryCoefficient t z.val := by
  obtain ⟨a,rfl⟩ := nativeReduction_surjective t z
  rw [epsilonCoefficient_of_reduction, val_mul, ← ordinaryEpsilon_native,
    ← ordinaryReduction_val, ordinaryCoefficient_of_reduction]

abbrev nativeCoefficients :=
  localizedCoefficients (ThickRing t) (ClosedRing t) (epsilonKernelEquiv t) p

private theorem epsilon_one :
    nativeThickMap t q p hq ((nativeCoefficients t p).epsilon 1) =
      (refinedCoefficients t q).epsilon 1 := by
  have hn := localizedCoefficients_epsilon_base (ThickRing t) (ClosedRing t) (epsilonKernelEquiv t) p (1 : ClosedRing t)
  have hc := refinedCoefficients_base t q (1 : ClosedCone t)
  rw [map_one] at hn hc
  rw [hn, nativeThickMap_base, hc]
  change algebraMap (ThickCone t) (RefinedThick t q) (epsilonCoefficient t 1).val = _
  rw [epsilon_val, val_one]

theorem nativeThickMap_coefficients (x : ClosedAt (ThickRing t) (ClosedRing t) p) :
    nativeThickMap t q p hq ((nativeCoefficients t p).epsilon x) =
      (refinedCoefficients t q).epsilon (nativeClosedMap t q p hq x) := by
  obtain ⟨a,rfl⟩ := localReduction_surjective (ThickRing t) (ClosedRing t) (nativeReduction_surjective t) p x
  have h := ((nativeCoefficients t p).epsilon_mul 1 a).symm
  rw [one_mul] at h
  rw [h, map_mul, epsilon_one, (refinedCoefficients t q).epsilon_mul, one_mul, nativeThickMap_reduction]

end CycleQ2IncidenceMarkedNativeCharts
end

#print axioms CycleQ2IncidenceMarkedNativeCharts.nativeThickMap_coefficients
#print axioms CycleQ2IncidenceMarkedNativeCharts.nativeTripleProduct_isUnit
