import Proposal.GeometricRelativeCanonicalCechLine

/-!
# The relative canonical component of a Laurent representative

Filtering the actual coordinate localization by degree gives its weight-three
component on each intersection. This projection commutes with arbitrary base
change, fixes homogeneous elements, and preserves the canonical trace.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2RelativeCanonicalProjection
open CycleQ2IncidenceNormalForm CycleQ2SeedCechThreeOpen CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates
  CycleQ2UniversalSurfaceCoefficientMap CycleQ2RelativeCanonicalLaurentTrace CycleQ2RelativeCanonicalCechLine

variable {R S : Type} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
variable (h : FullCubicTailIndex → R) (F : FullSexticTailIndex → R)

private def part (ab : ShiftIndex) (p : Laurent (R := R)) : Laurent (R := R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e => (shiftedGrade ab e).1 = 3))

private theorem part_coeff (ab : ShiftIndex) (p : Laurent (R := R)) (e : LaurentExponent) :
    (part ab p).coeff e = if (shiftedGrade ab e).1 = 3 then p.coeff e else 0 := rfl

private theorem exists_part (s : Finset (Fin 3)) (x : SurfaceLocal R h F s) :
    ∃ p, localizedCoordinates R h F s p = fun ab => part ab (localizedCoordinates R h F s x ab) := by
  apply (mem_range_localizedCoordinates R h F s _).mpr
  intro ab e i hi he
  rw [part_coeff, localizedCoordinates_hasPoles R h F s x ab e i hi he, ite_self]

def canonicalPart (s : Finset (Fin 3)) (x : SurfaceLocal R h F s) : weightThree h F s :=
  ⟨(exists_part h F s x).choose, by
    intro ab e he
    rw [(exists_part h F s x).choose_spec, part_coeff, if_neg he]⟩

theorem canonicalPart_coeff (s : Finset (Fin 3)) (x : SurfaceLocal R h F s) (ab : ShiftIndex) (e : LaurentExponent) :
    (localizedCoordinates R h F s (canonicalPart h F s x).val ab).coeff e =
      if (shiftedGrade ab e).1 = 3 then (localizedCoordinates R h F s x ab).coeff e else 0 := by
  change (localizedCoordinates R h F s (exists_part h F s x).choose ab).coeff e = _
  rw [(exists_part h F s x).choose_spec, part_coeff]

theorem canonicalPart_homogeneous (s : Finset (Fin 3)) (x : weightThree h F s) :
    canonicalPart h F s x.val = x := by
  apply Subtype.ext
  apply localizedCoordinates_injective R h F s
  funext ab
  ext e
  rw [canonicalPart_coeff]
  split <;> rename_i he
  · rfl
  · exact (x.property ab e he).symm

theorem canonicalPart_baseChange (f : R →+* S) (s : Finset (Fin 3)) (x : SurfaceLocal R h F s) :
    localMap f h F s (canonicalPart h F s x).val =
      (canonicalPart (fun i => f (h i)) (fun i => f (F i)) s (localMap f h F s x)).val := by
  apply localizedCoordinates_injective S _ _ s
  funext ab
  ext e
  simp only [coordinates_localMap, laurentMap_coeff, canonicalPart_coeff]
  split <;> simp

theorem canonicalPart_restrict {s t : Finset (Fin 3)} (hst : s ⊆ t) (x : SurfaceLocal R h F s) :
    restriction R h F hst (canonicalPart h F s x).val = (canonicalPart h F t (restriction R h F hst x)).val := by
  apply localizedCoordinates_injective R h F t
  funext ab
  ext e
  simp only [coordinates_restriction, canonicalPart_coeff]

/-- Class of an arbitrary ordinary localization element in the degree-three Čech quotient. -/
def canonicalClass (x : SurfaceLocal R h F Finset.univ) : (weightThree h F Finset.univ) ⧸ boundaries h F :=
  Submodule.Quotient.mk (canonicalPart h F Finset.univ x)

theorem canonicalClass_trace (x : SurfaceLocal R h F Finset.univ) :
    traceEquiv h F (canonicalClass h F x) = residue h F x := by
  simp only [traceEquiv, canonicalClass, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  change (localizedCoordinates R h F Finset.univ (canonicalPart h F Finset.univ x).val (2,2)).coeff
    (fun _ => -1) = _
  rw [canonicalPart_coeff, if_pos (by norm_num [shiftedGrade, Fin.sum_univ_succ])]
  rfl

end CycleQ2RelativeCanonicalProjection
end

#print axioms CycleQ2RelativeCanonicalProjection.canonicalClass_trace
#print axioms CycleQ2RelativeCanonicalProjection.canonicalPart_baseChange
