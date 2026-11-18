import Proposal.GeometricIncidenceMarkedCoefficientSections
import Proposal.GeometricIncidenceRelativeProjectorCocycle
import Proposal.GeometricFiniteRawTwoDescent

/-!
# The marked projective obstruction cochain

Project the actual universal cone faces to functions on the three
coordinate opens. The restrictions, four-face identity, and adjacent
repeated faces give a two-stage injective descent on the marked surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedProjectorDescent

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2IncidenceRelativeProjectorResidue CycleQ2IncidenceRelativeProjectorCocycle
  CycleQ2IncidenceMarkedCoefficientSections CycleQ2IncidenceCanonicalResidue
  CycleQ2IncidenceEtaleParameter CycleQ2UniversalSurfaceRestrictions
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2ProjectiveCoordinateCohomology

private abbrev Surface := CycleQ2IncidenceMarkedCoefficientSections.Surface
private abbrev Face := Finset (Fin 3)
private abbrev trip (i j k : Fin 3) : Face := {i,j,k}
private theorem le_trip (i j k : Fin 3) (W : Surface.Opens) (hi : W ≤ coordinate i)
    (hj : W ≤ coordinate j) (hk : W ≤ coordinate k) : W ≤ openOf (trip i j k) :=
  le_openOf _ _ (by
    intro a ha
    simp only [trip, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption)

private def tripleObstruction (i j k : Fin 3) :=
  obstruction (trip i j k) ⟨i,by simp [trip]⟩ ⟨j,by simp [trip]⟩ ⟨k,by simp [trip]⟩

def markedTwo : Two OS coordinate := fun i j k =>
  onOpen (trip i j k) (by simp [trip]) _ (le_trip i j k _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right) (tripleObstruction i j k)

/-- Every face has this formula on any larger set of coordinate indices. -/
theorem face_on (s : Face) (i j k : s) (W : Surface.Opens) (hW : W ≤ openOf s)
    (hi : W ≤ coordinate i.val) (hj : W ≤ coordinate j.val) (hk : W ≤ coordinate k.val) :
    faceValue OS coordinate markedTwo i.val j.val k.val W hi hj hk =
      onOpen s ⟨i.val,i.property⟩ W hW (obstruction s i j k) := by
  have inc : trip i.val j.val k.val ⊆ s := by
    intro a ha
    simp only [trip, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact i.property
    · exact j.property
    · exact k.property
  have he := obstruction_restrict inc
    (⟨i.val,by simp [trip]⟩ : trip i.val j.val k.val)
    ⟨j.val,by simp [trip]⟩ ⟨k.val,by simp [trip]⟩
  change restriction R cubic sextic inc (tripleObstruction _ _ _) = obstruction s i j k at he
  rw [← he, onOpen_restrict (by simp [trip]) _ inc]
  exact res_comp OS _ _ _

theorem markedTwo_repeat12 (i k : Fin 3) (W : Surface.Opens) (hi : W ≤ coordinate i)
    (hk : W ≤ coordinate k) : faceValue OS coordinate markedTwo i i k W hi hi hk = 0 := by
  rw [face_on (trip i i k) ⟨i,by simp [trip]⟩ ⟨i,by simp [trip]⟩ ⟨k,by simp [trip]⟩ W
    (le_trip i i k W hi hi hk) hi hi hk, obstruction_repeat12, map_zero]

theorem markedTwo_repeat23 (i j : Fin 3) (W : Surface.Opens) (hi : W ≤ coordinate i)
    (hj : W ≤ coordinate j) : faceValue OS coordinate markedTwo i j j W hi hj hj = 0 := by
  rw [face_on (trip i j j) ⟨i,by simp [trip]⟩ ⟨j,by simp [trip]⟩ ⟨j,by simp [trip]⟩ W
    (le_trip i j j W hi hj hj) hi hj hj, obstruction_repeat23, map_zero]

theorem markedTwo_closed : IsTwoCocycle OS coordinate markedTwo := by
  intro i j k l W hi hj hk hl
  let s : Face := {i,j,k,l}
  have hW : W ≤ openOf s := by
    apply le_openOf
    intro a ha
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  let ii : s := ⟨i,by simp [s]⟩
  let jj : s := ⟨j,by simp [s]⟩
  let kk : s := ⟨k,by simp [s]⟩
  let ll : s := ⟨l,by simp [s]⟩
  rw [face_on s jj kk ll W hW hj hk hl, face_on s ii kk ll W hW hi hk hl,
    face_on s ii jj ll W hW hi hj hl, face_on s ii jj kk W hW hi hj hk]
  simpa only [map_zero, map_sub, map_add] using congrArg (onOpen s ⟨i,ii.property⟩ W hW)
    (obstruction_closed s ii jj kk ll)

theorem exists_markedDescent : Nonempty (TwoDescent coordinate markedTwo) :=
  CycleQ2FiniteRawTwoDescent.exists_raw_descent coordinate (coordinate_cover 57 1 one_ne_zero) markedTwo
    markedTwo_repeat12 markedTwo_repeat23 markedTwo_closed

end CycleQ2IncidenceMarkedProjectorDescent
end

#print axioms CycleQ2IncidenceMarkedProjectorDescent.exists_markedDescent
