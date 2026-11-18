import Proposal.GeometricNormalizedCartierClass
import Proposal.GeometricLiteralCotangentTrace

/-!
# Canonical Laurent residue over a coefficient ring

For the normalized invariant complete intersections of weighted degrees
three and six, the nine monomials in x₀ and w give coordinates over the
three remaining variables. Extracting the coefficient of
x₀²w²/(x₁x₂x₃) is linear over the coefficient ring and kills every
pair-open boundary. It commutes with every change of coefficient ring,
and at the marked surface it gives the already normalized trace of
genuine canonical triple sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2RelativeCanonicalLaurentTrace
open CycleQ2IncidenceNormalForm CycleQ2UniversalSurface CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates
  CycleQ2UniversalSurfaceCoefficientMap
variable {A B : Type} [CommRing A] [Nontrivial A] [CommRing B] [Nontrivial B]
variable (h : FullCubicTailIndex → A) (F : FullSexticTailIndex → A)

/-- The top weighted coefficient on the actual normalized triple localization. -/
def residue : SurfaceLocal A h F Finset.univ →ₗ[A] A where
  toFun s := (localizedCoordinates A h F Finset.univ s (2,2)).coeff (fun _ => -1)
  map_add' p q := by simp only [map_add, Pi.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c p := by simp only [localizedCoordinates_R_smul, Pi.smul_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, RingHom.id_apply]

/-- The normalized residue is compatible with base change, including passage
from an incidence parameter ring to the residue field at a marked point. -/
theorem residue_baseChange (f : A →+* B) (p : SurfaceLocal A h F Finset.univ) :
    residue (fun i => f (h i)) (fun i => f (F i)) (localMap f h F Finset.univ p) =
      f (residue h F p) := by
  change (localizedCoordinates B _ _ _ _ _).coeff _ = _
  rw [coordinates_localMap, laurentMap_coeff]
  rfl

theorem residue_restrict_zero {s : Finset (Fin 3)} (i : Fin 3) (hi : i ∉ s) (p : SurfaceLocal A h F s) :
    residue h F (restriction A h F (Finset.subset_univ s) p) = 0 := by
  change (localizedCoordinates A h F Finset.univ _ (2,2)).coeff (fun _ => -1) = 0
  rw [coordinates_restriction]
  exact localizedCoordinates_hasPoles A h F s p (2,2) (fun _ => -1) i hi (by norm_num)

theorem residue_boundary (a : SurfaceLocal A h F {0,1}) (b : SurfaceLocal A h F {0,2})
    (c : SurfaceLocal A h F {1,2}) :
    residue h F (restriction A h F (Finset.subset_univ {1,2}) c -
      restriction A h F (Finset.subset_univ {0,2}) b + restriction A h F (Finset.subset_univ {0,1}) a) = 0 := by
  rw [map_add, map_sub, residue_restrict_zero h F 0 (by decide), residue_restrict_zero h F 1 (by decide),
    residue_restrict_zero h F 2 (by decide), sub_zero, add_zero]

open CycleQ2GeometricSeedNormalizedCoordinates CycleQ2CanonicalCoordinateH2
  CycleQ2CanonicalCoordinateCoefficients CycleQ2CanonicalResidueNonzero CycleQ2LiteralCotangentTrace
open CategoryTheory Opposite

/-- For a genuine 2-form on the marked triple open the relative coefficient
is exactly the algebraic trace of its cohomology class. -/
theorem marked_canonicalSection (s : CycleQ2CanonicalCoordinateH2.CanonicalSheaf.obj.obj (op CycleQ2CanonicalCoordinateH2.TripleOpen)) :
    residue (cubicCoefficients 57) (sexticCoefficients 57)
        (normalizedCoordinateEquiv 57 Finset.univ (canonicalCoefficient s)) =
      algebraicTrace (canonicalConnecting s) := by
  rw [algebraicTrace_eq]
  change (localizedCoordinates ℂ _ _ Finset.univ _ (2,2)).coeff (fun _ => -1) = _
  rw [normalizedCoordinateEquiv_coordinates]
  rfl

/-- The nonvanishing locus of the residue of a relative triple section
is cut out by a single coefficient in the actual parameter ring. -/
theorem specialization_ne_zero_iff (f : A →+* B) (p : SurfaceLocal A h F Finset.univ) :
    residue (fun i => f (h i)) (fun i => f (F i)) (localMap f h F Finset.univ p) ≠ 0 ↔
      residue h F p ∉ RingHom.ker f := by
  rw [residue_baseChange]
  rfl

end CycleQ2RelativeCanonicalLaurentTrace
end

#print axioms CycleQ2RelativeCanonicalLaurentTrace.residue_baseChange
#print axioms CycleQ2RelativeCanonicalLaurentTrace.marked_canonicalSection
