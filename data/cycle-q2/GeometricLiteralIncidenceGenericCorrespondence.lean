import Proposal.GeometricLiteralIncidenceRelativeCorrespondence
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The relative correspondence at the generic normalized sextic

Pulling the proper relative correspondence back to the fraction field of the
monic coefficient ring gives a proper surjective scheme for the chosen open
of each independent section triple. Its restriction to the corresponding
time open recovers the generic fibre of the original relative surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CycleQ2CoefficientBaseChange

noncomputable section

/-- The map between the fibre products over a new coefficient scheme. -/
def changeMap {S T X Y : Scheme.{0}} (η : T ⟶ S)
    {u : X ⟶ S} {v : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ v = u) :
    pullback u η ⟶ pullback v η :=
  ((Over.pullback η).map (Over.homMk f hf : Over.mk u ⟶ Over.mk v)).left

theorem changeMap_fst {S T X Y : Scheme.{0}} (η : T ⟶ S)
    {u : X ⟶ S} {v : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ v = u) :
    changeMap η f hf ≫ pullback.fst v η = pullback.fst u η ≫ f :=
  pullback.lift_fst _ _ _

theorem changeMap_snd {S T X Y : Scheme.{0}} (η : T ⟶ S)
    {u : X ⟶ S} {v : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ v = u) :
    changeMap η f hf ≫ pullback.snd v η = pullback.snd u η :=
  pullback.lift_snd _ _ _

/-- Pulling every object in a cartesian square back through the same coefficient
morphism gives a cartesian square of the schemes over the new coefficients. -/
theorem isPullback_changeMap {S T A B C D : Scheme.{0}} (η : T ⟶ S)
    {a : A ⟶ S} {b : B ⟶ S} {c : C ⟶ S} {d : D ⟶ S}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : f ≫ b = a) (hg : g ≫ c = a) (hi : i ≫ d = b) (hj : j ≫ d = c)
    (H : IsPullback f g i j) :
    IsPullback (changeMap η f hf) (changeMap η g hg) (changeMap η i hi) (changeMap η j hj) := by
  let f' : Over.mk a ⟶ Over.mk b := Over.homMk f hf
  let g' : Over.mk a ⟶ Over.mk c := Over.homMk g hg
  let i' : Over.mk b ⟶ Over.mk d := Over.homMk i hi
  let j' : Over.mk c ⟶ Over.mk d := Over.homMk j hj
  have H' : IsPullback f' g' i' j' := IsPullback.of_map_of_faithful (Over.forget S) H
  exact ((H'.map (Over.pullback η)).map (Over.forget T))

end

end CycleQ2CoefficientBaseChange


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2CoefficientBaseChange CycleQ2LiteralIncidenceRelativeCorrespondence
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

namespace CycleQ2LiteralIncidenceGenericCorrespondence

noncomputable section

abbrev genericField := FractionRing MonicRing

def genericPoint : Spec (CommRingCat.of genericField) ⟶ monicBase :=
  Spec.map (CommRingCat.ofHom (algebraMap MonicRing genericField))

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

private theorem fromSurface_over :
    fromSurface V t ≫ timeProjection V t ≫ structureMap V =
      curveMap toRaw V t ≫ timeMap toRaw V := by
  rw [← Category.assoc, fromSurface_toTime, Category.assoc, inclusion_over]

theorem genericOpen_pullback :
    IsPullback
      (changeMap genericPoint (v := timeMap toRaw V) (curveMap toRaw V t) rfl)
      (changeMap genericPoint (fromSurface V t) (fromSurface_over V t))
      (changeMap genericPoint (inclusion V) (inclusion_over V))
      (changeMap genericPoint (v := structureMap V) (timeProjection V t) rfl) :=
  isPullback_changeMap genericPoint rfl (fromSurface_over V t) (inclusion_over V) rfl
    (timeOpen_pullback V t)

abbrev genericCorrespondence :=
  pullback (timeProjection V t ≫ structureMap V) genericPoint

abbrev toGenericField : genericCorrespondence V t ⟶ Spec (CommRingCat.of genericField) :=
  pullback.snd _ _

theorem proper_surjective_generic_correspondence (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      IsProper (toGenericField V t) ∧ Function.Surjective (toGenericField V t) := by
  obtain ⟨W, hW, hproper, _, hsurjective, _⟩ := relative_correspondence_of_independent t hi
  let : IsProper (timeProjection W t ≫ structureMap W) := hproper
  let : Surjective (timeProjection W t ≫ structureMap W) := ⟨hsurjective⟩
  exact ⟨W, hW, inferInstance, (toGenericField W t).surjective⟩

end

end CycleQ2LiteralIncidenceGenericCorrespondence

#print axioms CycleQ2LiteralIncidenceGenericCorrespondence.genericOpen_pullback
#print axioms CycleQ2LiteralIncidenceGenericCorrespondence.proper_surjective_generic_correspondence
