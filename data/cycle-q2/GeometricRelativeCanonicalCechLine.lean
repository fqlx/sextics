import Proposal.GeometricRelativeCanonicalLaurentTrace

/-!
# The relative degree-three Laurent Čech quotient

On the three coordinate opens of every normalized (3,6) surface,
the canonical weight-three Čech quotient is the coefficient ring.
Its generator is the top basis monomial divided by x₁x₂x₃. All
other Laurent coefficients of weight three split off from pair opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
namespace CycleQ2RelativeCanonicalCechLine
open CycleQ2IncidenceNormalForm CycleQ2UniversalSurface CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions
  CycleQ2UniversalSurfaceLinearCoordinates CycleQ2UniversalSurfaceCoefficientMap
  CycleQ2GeometricLaurentTop CycleQ2RelativeCanonicalLaurentTrace
variable {A : Type} [CommRing A] [Nontrivial A] (h : FullCubicTailIndex → A) (F : FullSexticTailIndex → A)

/-- The genuine homogeneous degree-three pieces on every coordinate localization. -/
def weightThree (s : Finset (Fin 3)) : Submodule A (SurfaceLocal A h F s) where
  carrier := {x | ∀ ab e, (shiftedGrade ab e).1 ≠ 3 → (localizedCoordinates A h F s x ab).coeff e = 0}
  zero_mem' := by simp
  add_mem' hp hq := by
    intro ab e he
    simp only [map_add, Pi.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp ab e he, hq ab e he, add_zero]
  smul_mem' r p hp := by
    intro ab e he
    simp only [localizedCoordinates_R_smul, Pi.smul_apply, AddMonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, hp ab e he, smul_zero]

def restrictTop (s : Finset (Fin 3)) : weightThree h F s →ₗ[A] weightThree h F Finset.univ where
  toFun p := ⟨restrictionLinear A h F (Finset.subset_univ s) p.val, by
    intro ab e he
    change (localizedCoordinates A h F Finset.univ (restriction A h F (Finset.subset_univ s) p.val) ab).coeff e = 0
    rw [coordinates_restriction]
    exact p.property ab e he⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

def boundaries : Submodule A (weightThree h F Finset.univ) :=
  (restrictTop h F {0,1}).range ⊔ (restrictTop h F {0,2}).range ⊔ (restrictTop h F {1,2}).range

def traceSection : weightThree h F Finset.univ →ₗ[A] A :=
  (residue h F).comp (weightThree h F Finset.univ).subtype

private theorem pair_le_ker (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∉ s) :
    (restrictTop h F s).range ≤ (traceSection h F).ker := by
  rintro _ ⟨p,rfl⟩
  exact residue_restrict_zero h F i hi p.val

private def familyLift (s : Finset (Fin 3)) (g : ShiftIndex → Laurent (R := A))
    (hp : ∀ ab, HasPoles s (g ab)) (hw : ∀ ab e, (shiftedGrade ab e).1 ≠ 3 → (g ab).coeff e = 0) :
    weightThree h F s :=
  let hx := (mem_range_localizedCoordinates A h F s g).mpr hp
  ⟨hx.choose, by intro ab e he; rw [hx.choose_spec]; exact hw ab e he⟩

private theorem familyLift_spec (s : Finset (Fin 3)) (g : ShiftIndex → Laurent (R := A))
    (hp : ∀ ab, HasPoles s (g ab)) (hw : ∀ ab e, (shiftedGrade ab e).1 ≠ 3 → (g ab).coeff e = 0) :
    localizedCoordinates A h F s (familyLift h F s g hp hw).val = g :=
  ((mem_range_localizedCoordinates A h F s g).mpr hp).choose_spec

theorem boundaries_eq_ker : boundaries h F = (traceSection h F).ker := by
  apply le_antisymm
  · exact sup_le (sup_le (pair_le_ker h F _ 2 (by decide)) (pair_le_ker h F _ 1 (by decide)))
      (pair_le_ker h F _ 0 (by decide))
  intro p hp
  let v := localizedCoordinates A h F Finset.univ p.val
  have hneg (ab : ShiftIndex) (e : LaurentExponent) (he : ∀ i, e i < 0) : (v ab).coeff e = 0 := by
    by_cases hw : (shiftedGrade ab e).1 = 3
    · obtain ⟨rfl,rfl⟩ := strictlyNegative_weight_three_unique ab e he hw
      exact hp
    · exact p.property ab e hw
  let a := familyLift h F {0,1} (fun ab => pairPart01 (v ab)) (fun ab => pairPart01_hasPoles _)
    (by intro ab e he; simp only [pairPart01_coeff]; split <;> first | exact p.property ab e he | rfl)
  let b := familyLift h F {0,2} (fun ab => pairPart02 (v ab)) (fun ab => pairPart02_hasPoles _)
    (by intro ab e he; simp only [pairPart02_coeff]; split <;> first | exact p.property ab e he | rfl)
  let c := familyLift h F {1,2} (fun ab => pairPart12 (v ab)) (fun ab => pairPart12_hasPoles _ (hneg ab))
    (by intro ab e he; simp only [pairPart12_coeff]; split <;> first | exact p.property ab e he | rfl)
  have hs : restrictTop h F _ a + restrictTop h F _ b + restrictTop h F _ c = p := by
    apply Subtype.ext
    apply localizedCoordinates_injective A h F Finset.univ
    funext ab
    change localizedCoordinates A h F Finset.univ
      (restriction A h F (Finset.subset_univ _) a.val + restriction A h F (Finset.subset_univ _) b.val + restriction A h F (Finset.subset_univ _) c.val) ab = v ab
    simp only [map_add, Pi.add_apply, coordinates_restriction, a,b,c,familyLift_spec]
    exact pairParts_sum _
  rw [← hs]
  apply Submodule.add_mem_sup
  · apply Submodule.add_mem_sup
    · exact ⟨a,rfl⟩
    · exact ⟨b,rfl⟩
  · exact ⟨c,rfl⟩

theorem traceSection_surjective : Function.Surjective (traceSection h F) := by
  classical
  intro a
  let g (ab : ShiftIndex) : Laurent (R := A) :=
    if ab = (2,2) then AddMonoidAlgebra.single (fun _ : Fin 3 => (-1 : ℤ)) a else 0
  have hp (ab) : HasPoles Finset.univ (g ab) := by intro e i hi; simp at hi
  have hw (ab e) (he : (shiftedGrade ab e).1 ≠ 3) : (g ab).coeff e = 0 := by
    by_cases ha : ab = (2,2)
    · subst ab
      have hn : e ≠ fun _ : Fin 3 => (-1 : ℤ) := by
        rintro rfl
        exact he (by norm_num [shiftedGrade, Fin.sum_univ_succ])
      simp [g, AddMonoidAlgebra.coeff_single, hn]
    · simp [g,ha]
  refine ⟨familyLift h F Finset.univ g hp hw,?_⟩
  change (localizedCoordinates A h F Finset.univ (familyLift h F Finset.univ g hp hw).val (2,2)).coeff _ = a
  rw [familyLift_spec]
  simp [g, AddMonoidAlgebra.coeff_single]

/-- The canonical coordinate Čech line over the entire coefficient ring. -/
def traceEquiv : ((weightThree h F Finset.univ) ⧸ boundaries h F) ≃ₗ[A] A :=
  (Submodule.quotEquivOfEq _ _ (boundaries_eq_ker h F)).trans
    ((traceSection h F).quotKerEquivOfSurjective (traceSection_surjective h F))

end CycleQ2RelativeCanonicalCechLine
end

#print axioms CycleQ2RelativeCanonicalCechLine.traceEquiv
