import Proposal.GeometricLiteralIncidenceGenericModel
import Proposal.GeometricLiteralIncidenceComplexTest
import Proposal.GeometricIncidenceRelativeProjectorSpecialization

/-!
# Nonzero projector residues on the generic and complex time fibers

The regular coefficient defining the incidence projector residue is evaluated at
actual incidence points. A nonzero marked value yields a finite étale extension
of the monic coefficient function field carrying a nonzero fiber residue. It
also yields such a residue at a complex point above any nonempty coefficient open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IncidenceProjectorTestSpread

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceGenericModel CycleQ2LiteralIncidenceComplexTest
  CycleQ2LiteralIncidenceRelativeNormalization CycleQ2IncidenceRelativeProjectorResidue
  CycleQ2IncidenceRelativeProjectorSpecialization CycleQ2RelativeCanonicalLaurentTrace
  CycleQ2FiniteEtaleParameterPoint

variable (V : parameterScheme.Opens)

abbrev timeParameters : Time toRaw V ⟶ parameterScheme :=
  pullback.snd toRaw (V.ι ≫ parameterToSextics) ≫ V.ι

abbrev testOpen : (Time toRaw V).Opens :=
  timeParameters V ⁻¹ᵁ PrimeSpectrum.basicOpen regularCoefficient

abbrev genericTime : TimeFiber V ⟶ Time toRaw V :=
  pullback.snd (pullback.snd genericMorphism (normalizedMap V)) (openInclusion V)

private theorem eval_nonzero {L : Type} [Field L] (s : Spec (CommRingCat.of L) ⟶ parameterScheme)
    (a : ParameterAlgebra) : s default ∈ PrimeSpectrum.basicOpen a ↔ (Spec.preimage s).hom a ≠ 0 := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective s
  rw [Spec.preimage_map, PrimeSpectrum.mem_basicOpen, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap, Ideal.eq_bot_of_prime] <;> rfl

abbrev markedTime (hV : seedBasePoint ∈ V) :=
  seedLift V hV ≫ fixedToTime toRaw V seedPoint seedPoint_toRaw

private theorem marked_over (hV : seedBasePoint ∈ V) : markedTime V hV ≫ timeMap toRaw V = seedPoint := by
  have h : seed ≫ CycleQ2LiteralIncidenceTimeCurve.toComplex = 𝟙 _ := pullback.lift_fst _ _ _
  simp only [markedTime, Category.assoc, fixedToTime_fst, seedLift_fac_assoc, ← Category.assoc seed, h,
    Category.id_comp]

theorem marked_mem_testOpen (hV : seedBasePoint ∈ V) (h : seedMap regularCoefficient ≠ 0) :
    markedTime V hV default ∈ testOpen V := by
  have hs : markedTime V hV ≫ timeParameters V = seedPointMorphism := by
    simp only [markedTime, timeParameters, Category.assoc, fixedToTime_snd_assoc, morphismRestrict_ι,
      seedLift_fac_assoc, seed_to_incidence]
  change (markedTime V hV ≫ timeParameters V) default ∈ PrimeSpectrum.basicOpen regularCoefficient
  rw [hs, eval_nonzero, seedPointMorphism, Spec.preimage_map]
  exact h

theorem marked_testOpen (hV : seedBasePoint ∈ V) (h : seedMap regularCoefficient ≠ 0) :
    (testOpen V : Set (Time toRaw V)).Nonempty := ⟨_, marked_mem_testOpen V hV h⟩

abbrev evalComplex (s : Spec (CommRingCat.of ℂ) ⟶ Time toRaw V) : ParameterAlgebra →+* ℂ :=
  (Spec.preimage (s ≫ timeParameters V)).hom

abbrev evalGeneric (x : TimeFiber V) : ParameterAlgebra →+* (TimeFiber V).residueField x :=
  (Spec.preimage ((TimeFiber V).fromSpecResidueField x ≫ genericTime V ≫ timeParameters V)).hom

/-- The specialized cup has nonzero residue at an actual complex incidence point above
each prescribed nonempty open of the full coefficient space. -/
theorem complex_nonzero (hV : seedBasePoint ∈ V) (h : seedMap regularCoefficient ≠ 0)
    (U : monicBase.Opens) (hU : (U : Set monicBase).Nonempty) :
    ∃ s : Spec (CommRingCat.of ℂ) ⟶ Time toRaw V,
      s ≫ timeMap toRaw V ≫ CycleQ2LiteralIncidenceNormalizedSlice.toComplex = 𝟙 _ ∧
      timeMap toRaw V (s default) ∈ U ∧
      residue (cubicFiber (evalComplex V s)) (sexticFiber (evalComplex V s))
        (fiberCup (evalComplex V s)) ≠ 0 := by
  obtain ⟨s, hs, hx, hu⟩ := complex_point_over_open V _ (marked_testOpen V hV h) U hU
  refine ⟨s, hs, hu, ?_⟩
  rw [fiber_residue]
  exact (eval_nonzero (s ≫ timeParameters V) _).mp hx

/-- Every complex coefficient point in a single open neighborhood of the marked
sextic admits a lift with nonzero specialized projector residue. -/
theorem complex_nonzero_neighborhood (hV : seedBasePoint ∈ V) (h : seedMap regularCoefficient ≠ 0) :
    ∃ D : monicBase.Opens, seedPoint default ∈ D ∧
      ∀ b : Spec (CommRingCat.of ℂ) ⟶ monicBase, b default ∈ D →
        ∃ s : Spec (CommRingCat.of ℂ) ⟶ Time toRaw V, s ≫ timeMap toRaw V = b ∧
          residue (cubicFiber (evalComplex V s)) (sexticFiber (evalComplex V s))
            (fiberCup (evalComplex V s)) ≠ 0 := by
  let u := (testOpen V).ι ≫ timeMap toRaw V
  have := timeMap_smooth toRaw V
  have : Smooth (timeMap toRaw V) := SmoothOfRelativeDimension.smooth 1 _
  let D : monicBase.Opens := ⟨Set.range u, u.isOpenMap.isOpen_range⟩
  refine ⟨D, ?_, ?_⟩
  · refine ⟨⟨_, marked_mem_testOpen V hV h⟩, ?_⟩
    change (markedTime V hV ≫ timeMap toRaw V) default = _
    rw [marked_over]
  intro b hb
  obtain ⟨y, hy⟩ := hb
  let Z : Scheme := pullback b u
  let f : Z ⟶ Spec (CommRingCat.of ℂ) := pullback.fst _ _
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := b) (g := u) default y hy.symm
  have : Nonempty Z := ⟨z⟩
  obtain ⟨x, _, he, _, _, _⟩ := exists_finite_etale_closedPoint f
  let _ : Algebra ℂ (Z.residueField x) := (pointFieldMap f x).hom.toAlgebra
  let _ : Module.Finite ℂ (Z.residueField x) := he
  have hbije : Function.Bijective (pointFieldMap f x).hom := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
  let e := (RingEquiv.ofBijective (pointFieldMap f x).hom hbije).toCommRingCatIso
  let c := Spec.map e.inv ≫ Z.fromSpecResidueField x
  have hc : c ≫ f = 𝟙 _ := by
    rw [Category.assoc, ← pointFieldMap_spec, ← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map e.hom_inv_id
  let a := c ≫ pullback.snd b u
  refine ⟨a ≫ (testOpen V).ι, ?_, ?_⟩
  · change (a ≫ (testOpen V).ι) ≫ timeMap toRaw V = b
    rw [Category.assoc]
    change (c ≫ pullback.snd b u) ≫ u = b
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    change (c ≫ f) ≫ b = b
    rw [hc, Category.id_comp]
  · rw [fiber_residue]
    apply (eval_nonzero ((a ≫ (testOpen V).ι) ≫ timeParameters V) _).mp
    exact (a default).property

/-- A closed point on the actual generic time fiber carries nonzero residue, over a finite
étale extension of the monic sextic function field. -/
theorem generic_nonzero (hV : seedBasePoint ∈ V) (h : seedMap regularCoefficient ≠ 0) :
    ∃ x : TimeFiber V, IsClosed {x} ∧
      IsFinite ((TimeFiber V).fromSpecResidueField x ≫ inclusion V ≫ projection V) ∧
      Etale ((TimeFiber V).fromSpecResidueField x ≫ inclusion V ≫ projection V) ∧
      residue (cubicFiber (evalGeneric V x)) (sexticFiber (evalGeneric V x))
        (fiberCup (evalGeneric V x)) ≠ 0 := by
  let W := genericTime V ⁻¹ᵁ testOpen V
  have hW : (W : Set (TimeFiber V)).Nonempty := test_meets_generic V _ (marked_testOpen V hV h)
  have : Smooth (inclusion V ≫ projection V) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨x, hx, hc, _, hf, he, _⟩ := exists_finite_etale_closedPoint_in
    (inclusion V ≫ projection V) (W : Set (TimeFiber V)) hW W.isOpen.isLocallyClosed
  refine ⟨x, hc, hf, he, ?_⟩
  rw [fiber_residue]
  apply (eval_nonzero ((TimeFiber V).fromSpecResidueField x ≫ genericTime V ≫ timeParameters V) _).mp
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  exact hx

end CycleQ2IncidenceProjectorTestSpread
end

#print axioms CycleQ2IncidenceProjectorTestSpread.complex_nonzero
#print axioms CycleQ2IncidenceProjectorTestSpread.complex_nonzero_neighborhood
#print axioms CycleQ2IncidenceProjectorTestSpread.generic_nonzero
