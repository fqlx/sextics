import Proposal.GeometricLiteralTimeCurveLocalNormal
import Proposal.GeometricLiteralTimeNormalizationFinite
import Proposal.GeometricLiteralAbelJacobiTimeFamily

/-!
# A marked affine integral open inside the smooth time curve

A domain stalk on a Noetherian affine scheme has a principal integral neighborhood.
The kernel of the localization is finitely generated, so a single element outside
the prime kills this kernel. The resulting principal open can be chosen inside
the given time open. Its projective closure and finite normalization are integral
and retain the original marked infinitesimal point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeMarkedIntegralBranch

open CategoryTheory AlgebraicGeometry TopologicalSpace Set

private theorem finite_kernel_denominator {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] (P : Submonoid A) [IsLocalization P B] (T : Finset A)
    (h : ∀ a ∈ T, algebraMap A B a = 0) : ∃ d : P, ∀ a ∈ T, (d : A) * a = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a T ha ih =>
    obtain ⟨d,hd⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨e,he⟩ := (IsLocalization.map_eq_zero_iff P B a).mp (h a (Finset.mem_insert_self _ _))
    refine ⟨e*d, fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with hba | hb
    · rw [hba]
      change ((e : A) * d) * a = 0
      rw [mul_right_comm, he, zero_mul]
    · change ((e : A) * d) * b = 0
      rw [mul_assoc, hd b hb, mul_zero]

private theorem domain_away {A B : Type} [CommRing A] [CommRing B] [IsNoetherianRing A]
    [IsDomain B] [Algebra A B] (P : Submonoid A) [IsLocalization P B] :
    ∃ s : P, ∀ (C : Type) [CommRing C] [Algebra A C] [IsLocalization.Away (s : A) C], IsDomain C := by
  let I := RingHom.ker (algebraMap A B)
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian I)
  have hgen : Ideal.span (T : Set A) = I := hT
  obtain ⟨s, hs⟩ := finite_kernel_denominator (B := B) P T (fun a ha =>
    show a ∈ I from hgen ▸ Ideal.subset_span ha)
  refine ⟨s, ?_⟩
  intro C _ _ hC
  let f : C →+* B := IsLocalization.Away.lift (s : A) (IsLocalization.map_units B s)
  have hker : I ≤ RingHom.ker (algebraMap A C) := by
    rw [← hgen]
    exact Ideal.span_le.mpr fun a ha =>
      (IsLocalization.map_eq_zero_iff (.powers (s : A)) C a).mpr
        ⟨⟨_, Submonoid.mem_powers _⟩, hs a ha⟩
  have hfinj : Function.Injective f := by
    apply hC.injective_of_map_algebraMap_zero
    intro x hx
    exact hker (show x ∈ I from (IsLocalization.Away.lift_eq _ _ _).symm.trans hx)
  exact hfinj.isDomain f

private theorem principal_integral {X : Scheme.{0}} [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (x : X) [IsDomain (X.presheaf.stalk x)] (V : X.Opens) (hx : x ∈ V) :
    ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧ X.basicOpen s ≤ V ∧ IsIntegral (X.basicOpen s).toScheme := by
  let x' : (⊤ : X.Opens) := ⟨x, trivial⟩
  let p := (isAffineOpen_top X).primeIdealOf x'
  letI : Algebra Γ(X, ⊤) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal := (isAffineOpen_top X).isLocalization_stalk x'
  obtain ⟨d,hd⟩ := domain_away (B := X.presheaf.stalk x) p.asIdeal.primeCompl
  let W := X.basicOpen (d : Γ(X, ⊤))
  have hw : x ∈ W := (X.mem_basicOpen_top _ x).mpr (IsLocalization.map_units (X.presheaf.stalk x) d)
  have hWI : IsAffineOpen W := (isAffineOpen_top X).basicOpen _
  letI : IsDomain Γ(X, W) := hd _
  letI : IsIntegral W.toScheme := IsIntegral.of_isIso hWI.isoSpec.inv
  obtain ⟨v, hv, hmem⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := V ⊓ W) ⟨x, hx, hw⟩ trivial
  letI : Nonempty (X.basicOpen v).toScheme := ⟨⟨x,hmem⟩⟩
  exact ⟨v, hmem, hv.trans inf_le_left,
    isIntegral_of_isOpenImmersion (X.homOfLE (hv.trans inf_le_right))⟩

open CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralTimeCurveAffineEmbedding
  CycleQ2LiteralTimeCurveCompletion CycleQ2LiteralTimeCurveNormalization
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2IncidenceFirstOrder CycleQ2FirstOrderNeighborhood
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

abbrev markedPoint : Curve := seed (default : Spec (CommRingCat.of ℂ))

private theorem exists_branch (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V) :
    ∃ s : CoordinateRing, markedPoint ∈ Curve.basicOpen s ∧ Curve.basicOpen s ≤ timeOpen V ∧
      IsIntegral (Curve.basicOpen s).toScheme := by
  letI := CycleQ2LiteralTimeCurveLocalNormal.stalk_isDomain markedPoint
  letI := coordinate_finiteType
  letI := Algebra.FiniteType.isNoetherianRing ℂ CoordinateRing
  apply principal_integral
  change (seed ≫ toIncidence) (default : Spec (CommRingCat.of ℂ)) ∈ V
  rw [seed_to_incidence]
  exact hV

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

/-- A function defining a marked integral principal open of the original affine curve. -/
def function : CoordinateRing := (exists_branch V hV).choose

abbrev branch : Curve.Opens := Curve.basicOpen (function V hV)

theorem marked_mem : markedPoint ∈ branch V hV := (exists_branch V hV).choose_spec.1

theorem branch_le : branch V hV ≤ timeOpen V := (exists_branch V hV).choose_spec.2.1

theorem branch_affine : IsAffineOpen (branch V hV) := (isAffineOpen_top Curve).basicOpen _

instance branch_integral : IsIntegral (branch V hV).toScheme := (exists_branch V hV).choose_spec.2.2

/-- Inclusion in the prescribed smooth time open. -/
def toTime : (branch V hV).toScheme ⟶ (timeOpen V).toScheme := Curve.homOfLE (branch_le V hV)

instance : IsOpenImmersion (toTime V hV) := inferInstanceAs (IsOpenImmersion (Curve.homOfLE _))

def branchSeed : Spec (CommRingCat.of ℂ) ⟶ (branch V hV).toScheme :=
  IsOpenImmersion.lift (branch V hV).ι seed (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim z default]
    exact marked_mem V hV)

@[reassoc (attr := simp)] theorem branchSeed_fac : branchSeed V hV ≫ (branch V hV).ι = seed :=
  IsOpenImmersion.lift_fac _ _ _

def branchTangent : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ (branch V hV).toScheme :=
  IsOpenImmersion.lift (branch V hV).ι timeTangent (by
    rintro _ ⟨z,rfl⟩
    rw [Scheme.Opens.range_ι, firstOrderPoint_eq_closedPoint z]
    change (firstOrderClosedPoint ≫ timeTangent) _ ∈ branch V hV
    rw [timeTangent_at_seed]
    exact marked_mem V hV)

@[reassoc (attr := simp)] theorem branchTangent_fac :
    branchTangent V hV ≫ (branch V hV).ι = timeTangent := IsOpenImmersion.lift_fac _ _ _

theorem branchTangent_at_seed : firstOrderClosedPoint ≫ branchTangent V hV = branchSeed V hV := by
  apply (cancel_mono (branch V hV).ι).mp
  rw [Category.assoc, branchTangent_fac, branchSeed_fac, timeTangent_at_seed]

@[reassoc (attr := simp)] theorem branchSeed_toTime :
    branchSeed V hV ≫ toTime V hV = seedLift V hV := by
  apply (cancel_mono (timeOpen V).ι).mp
  rw [Category.assoc, toTime, Scheme.homOfLE_ι, branchSeed_fac, seedLift_fac]

@[reassoc (attr := simp)] theorem branchTangent_toTime :
    branchTangent V hV ≫ toTime V hV = tangentLift V hV := by
  apply (cancel_mono (timeOpen V).ι).mp
  rw [Category.assoc, toTime, Scheme.homOfLE_ι, branchTangent_fac, tangentLift_fac]

theorem branchTangent_nonconstant : branchTangent V hV ≠ structureDual ≫ branchSeed V hV := by
  intro h
  apply timeTangent_nonconstant
  simpa only [Category.assoc, branchTangent_fac, branchSeed_fac] using congrArg (· ≫ (branch V hV).ι) h

private theorem integralTarget {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsDominant f] [IsIntegral X] [AlgebraicGeometry.IsReduced Y] : IsIntegral Y := by
  have hr : IsIrreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn
  letI : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr (by
    change IsIrreducible (Set.univ : Set Y)
    rw [← f.denseRange.closure_eq]
    exact hr.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

instance completion_integral : IsIntegral (Completion (branch V hV)) :=
  integralTarget (inclusion (branch V hV))

instance normalization_integral : IsIntegral (Normalization (branch V hV)) := by
  letI : AlgebraicGeometry.IsReduced (Normalization (branch V hV)) :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (inclusion (branch V hV)).normalization)
  exact integralTarget (openInclusion (branch V hV))

/-- Every affine open of the completion meets the branch in an affine open. -/
instance inclusion_affine : IsAffineHom (inclusion (branch V hV)) :=
  IsAffineHom.of_comp (inclusion (branch V hV)) (structureMap (branch V hV))

/-- The same intersection property holds on the proper finite normalization. -/
instance normalizationInclusion_affine : IsAffineHom (openInclusion (branch V hV)) :=
  IsAffineHom.of_comp (openInclusion (branch V hV)) (toComplexPoint (branch V hV))

/-- After normalization the full marked dual-number morphism is still nonconstant. -/
theorem normalizedTangent_nonconstant :
    branchTangent V hV ≫ openInclusion (branch V hV) ≠
      structureDual ≫ branchSeed V hV ≫ openInclusion (branch V hV) := by
  rw [← Category.assoc]
  exact preserves_distinct_maps _ (branchTangent_nonconstant V hV)

#print axioms branch_integral
#print axioms completion_integral
#print axioms normalization_integral
#print axioms inclusion_affine
#print axioms normalizedTangent_nonconstant

end CycleQ2LiteralTimeMarkedIntegralBranch
end
