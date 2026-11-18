import Proposal.GeometricLiteralIncidenceCylinderMap
import Proposal.GeometricIncidenceSeedFiber

/-!
# The normalized sextic coefficient slice through the marked incidence point

The actual seed evaluates all raw sextic coefficients at those of the
polynomial smoothF(57,I). Its coefficient of w³ is one. Fixing precisely
this coordinate embeds the affine space of monic sextics into the raw
coefficient space. The marked complex point factors through this slice.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralIncidenceNormalizedSlice

open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2IncidenceMonomials CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceImageLine CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceFamilyContainment

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

abbrev MonicRing := MvPolynomial FullSexticTailIndex ℂ

def monicBase : Scheme := Spec (CommRingCat.of MonicRing)

abbrev rawSeedEval : CycleQ2IncidenceTimeCurve.SexticRing →+* ℂ :=
  seedMap.comp sexticToParameter

@[simp] theorem rawSeedEval_C (a : ℂ) : rawSeedEval (C a) = a :=
  (congrArg seedMap (CycleQ2GenericTimeDerivation.sexticToParameter_C a)).trans
    (CycleQ2IncidenceSeedFiber.seedMap_complex a)

@[simp] theorem rawSeedEval_X (e : FullInvariantIndex 6) :
    rawSeedEval (X e) = seedSexticCoefficients (57 : ℂ) Complex.I e := by
  change seedMap (sexticToParameter (X e)) = _
  rw [sexticToParameter_X, seedMap_algebraMap]
  simp [seedEvaluation, sexticParameter, baseSeed]

theorem seed_leading : seedSexticCoefficients (57 : ℂ) Complex.I fullSexticLeadingIndex = 1 := by
  simp only [seedSexticCoefficients, fullSexticLeadingIndex_exponent, smoothF_leading_coefficient]

theorem rawSeedEval_leading : rawSeedEval (X fullSexticLeadingIndex) = 1 :=
  (rawSeedEval_X _).trans seed_leading

def rawCoordinate (e : FullInvariantIndex 6) : MonicRing :=
  if h : (e.val 4).val < 3 then X ⟨e,h⟩ else 1

@[simp] theorem rawCoordinate_tail (e : FullSexticTailIndex) :
    rawCoordinate e.val = X e := by simp [rawCoordinate, e.property]

@[simp] theorem rawCoordinate_leading : rawCoordinate fullSexticLeadingIndex = 1 := by
  have h := (fullSextic_tail_iff_ne fullSexticLeadingIndex).not.mpr (not_not.mpr rfl)
  simp [rawCoordinate, h]

def rawToMonic : CycleQ2IncidenceTimeCurve.SexticRing →+* MonicRing :=
  eval₂Hom C rawCoordinate

@[simp] theorem rawToMonic_C (a : ℂ) : rawToMonic (C a) = C a := by simp [rawToMonic]
@[simp] theorem rawToMonic_X (e : FullInvariantIndex 6) : rawToMonic (X e) = rawCoordinate e := by
  simp [rawToMonic]

def toRaw : monicBase ⟶ sexticBase := Spec.map (CommRingCat.ofHom rawToMonic)

theorem rawToMonic_surjective : Function.Surjective rawToMonic := by
  let inc := (rename (Subtype.val : FullSexticTailIndex → FullInvariantIndex 6) :
    MonicRing →ₐ[ℂ] CycleQ2IncidenceTimeCurve.SexticRing)
  have h : rawToMonic.comp inc.toRingHom = RingHom.id MonicRing := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [inc]
    · intro e
      simp [inc]
  exact fun p => ⟨inc p, congrArg (fun f : MonicRing →+* MonicRing => f p) h⟩

instance toRaw_isClosedImmersion : IsClosedImmersion toRaw :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom rawToMonic) rawToMonic_surjective

def toComplex : monicBase ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ MonicRing))

@[reassoc, simp] theorem toRaw_over :
    toRaw ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ CycleQ2IncidenceTimeCurve.SexticRing)) =
      toComplex := by
  rw [toRaw, toComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext rawToMonic_C)

/-- The original universal projective equation becomes the normalized full sextic
with its independent tail coefficients on this slice. -/
theorem universal_equation :
    MvPolynomial.map rawToMonic (pointEquationF universalPoint) =
      normalizedFullSextic (fun e : FullSexticTailIndex => (X e : MonicRing)) := by
  rw [pointEquationF, pointMap_familyF, map_fullInvariantPolynomial]
  have h : rawToMonic ∘ pointSextic universalPoint = rawCoordinate := by
    funext e
    exact rawToMonic_X e
  rw [h, fullInvariantPolynomial_sextic, rawCoordinate_leading]
  simp only [rawFullSextic, normalizedFullSextic, rawCoordinate_tail]

def monicSeedEval : MonicRing →+* ℂ :=
  eval (fun e : FullSexticTailIndex => seedSexticCoefficients (57 : ℂ) Complex.I e.val)

def seedPoint : Spec (CommRingCat.of ℂ) ⟶ monicBase := Spec.map (CommRingCat.ofHom monicSeedEval)

@[reassoc, simp] theorem seedPoint_over : seedPoint ≫ toComplex = 𝟙 _ := by
  rw [seedPoint, toComplex, ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun c => eval_C c)

theorem monicSeedEval_comp : monicSeedEval.comp rawToMonic = rawSeedEval := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [monicSeedEval]
  · intro e
    rw [RingHom.comp_apply, rawToMonic_X, rawSeedEval_X]
    by_cases h : (e.val 4).val < 3
    · simp [rawCoordinate, h, monicSeedEval]
    · have he : e = fullSexticLeadingIndex := not_not.mp ((fullSextic_tail_iff_ne e).not.mp h)
      subst e
      rw [rawCoordinate_leading, map_one, seed_leading]

@[reassoc, simp] theorem seedPoint_toRaw : seedPoint ≫ toRaw = seedSextic := by
  rw [seedPoint, toRaw, seedSextic, seedPointMorphism, parameterToSextics, ← Spec.map_comp,
    ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext monicSeedEval_comp

end CycleQ2LiteralIncidenceNormalizedSlice

end

#print axioms CycleQ2LiteralIncidenceNormalizedSlice.universal_equation
#print axioms CycleQ2LiteralIncidenceNormalizedSlice.seedPoint_toRaw
