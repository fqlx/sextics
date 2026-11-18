import Proposal.GeometricGenericPencilLift
import Proposal.GeometricLiteralOrbitAction
import Proposal.GeometricHodgeThreefold
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The weighted quotient equation of the protected generic pencil

The base field is the rational function field in the pencil parameter itself.
The weighted equation is the exact restriction of the original protected sextic
along Y₂ = λ X₂ after the substitution w = X₂². The coefficient of w³ is a unit
over this field, so the four weight-one opens cover its projective hypersurface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ProtectedGenericPencilModel

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2IncidenceNormalForm CycleQ2GeometricIncidenceProj CycleQ2SeedCyclicAction

abbrev K := RatFunc ℂ
def parameter : K := RatFunc.X
abbrev P := MvPolynomial (Fin 5) K

def square : P →ₐ[K] P := aeval ![X 0, X 1, X 2, X 3, X 4 ^ 2]

def restrictProtected : HodgeComputer.AmbientPoly 5 →ₐ[ℂ] P :=
  aeval ![X 0, X 1, X 4, X 2, X 3, C parameter * X 4]

def G : P :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + C (1 + parameter ^ 6) * X 4 ^ 3 +
    C (1 / 2 : K) * (X 0 ^ 3 * X 1 * X 2 * X 3 +
      C parameter * X 1 ^ 3 * X 3 * X 4 + C parameter * X 0 * X 2 * X 4 ^ 2)

theorem restrictProtected_F : restrictProtected HodgeSubmission.F = square G := by
  have ht : RatFunc.C (2 : ℂ) = (2 : K) := map_ofNat _ _
  simp [restrictProtected, HodgeSubmission.F, square, G, ht, one_div]
  ring

theorem vertexCoefficient_ne_zero : 1 + parameter ^ 6 ≠ 0 := by
  have h : (1 + Polynomial.X ^ 6 : Polynomial ℂ) ≠ 0 := by
    intro h
    have e := congrArg (Polynomial.eval (0 : ℂ)) h
    simpa using e
  have hx := (RatFunc.algebraMap_injective ℂ).ne h
  simpa [parameter] using hx

theorem G_vertexCoefficient : G.coeff (Finsupp.single 4 3) = 1 + parameter ^ 6 := by
  have factor : G = X 0 * (X 0 ^ 5 + C (1 / 2 : K) *
        (X 0 ^ 2 * X 1 * X 2 * X 3 + C parameter * X 2 * X 4 ^ 2)) +
      X 1 * (X 1 ^ 5 + C (1 / 2 : K) * C parameter * X 1 ^ 2 * X 3 * X 4) +
      X 2 * X 2 ^ 5 + X 3 * X 3 ^ 5 + C (1 + parameter ^ 6) * X 4 ^ 3 := by
    unfold G
    ring
  rw [factor]
  simp only [coeff_add, coeff_X_mul', coeff_C_mul, coeff_X_pow,
    Finsupp.support_single _ (by decide : (3 : ℕ) ≠ 0), Finset.mem_singleton,
    (by decide : (0 : Fin 5) ≠ 4), (by decide : (1 : Fin 5) ≠ 4),
    (by decide : (2 : Fin 5) ≠ 4), (by decide : (3 : Fin 5) ≠ 4),
    ite_false, if_pos rfl, zero_add, mul_one] <;> norm_num

def monicNormalization : P := C (1 + parameter ^ 6)⁻¹ * G

theorem monicNormalization_vertexCoefficient :
    monicNormalization.coeff (Finsupp.single 4 3) = 1 := by
  rw [monicNormalization, coeff_C_mul, G_vertexCoefficient, inv_mul_cancel₀ vertexCoefficient_ne_zero]

theorem monicNormalization_ideal :
    Ideal.span ({monicNormalization} : Set P) = Ideal.span {G} :=
  Ideal.span_singleton_mul_left_unit
    ((isUnit_iff_ne_zero.mpr vertexCoefficient_ne_zero).inv.map (C : K →+* P)) G

private def constantFiber (l : ℂ) : P :=
  MvPolynomial.map (algebraMap ℂ K) (CycleQ2GenericPencilLift.weightedPencil l)

private theorem constantFiber_homogeneous (l : ℂ) :
    (constantFiber l).IsWeightedHomogeneous fullGrading (6, 0) := by
  intro e he
  apply CycleQ2GenericPencilLift.weightedPencil_homogeneous l
  intro hc
  apply he
  simp [constantFiber, coeff_map, hc]

/-- Interpolation in the linear and sixth-power terms recovers the generic
member from the existing protected weighted-pencil equations at zero and one. -/
private theorem G_interpolate :
    G = constantFiber 0 +
      C parameter * (constantFiber 1 - constantFiber 0 - X 4 ^ 3) +
      C (parameter ^ 6) * X 4 ^ 3 := by
  have ht : RatFunc.C (2 : ℂ) = (2 : K) := map_ofNat _ _
  simp [constantFiber, CycleQ2GenericPencilLift.weightedPencil, G, C_add, map_pow, ht, one_div]
  ring

theorem G_fullHomogeneous : G.IsWeightedHomogeneous fullGrading (6, 0) := by
  have hw : (X 4 ^ 3 : P).IsWeightedHomogeneous fullGrading (6, 0) := by
    convert (isWeightedHomogeneous_X K fullGrading (4 : Fin 5)).pow 3 using 1 <;> decide
  rw [G_interpolate]
  exact ((constantFiber_homogeneous 0).add (((constantFiber_homogeneous 1).sub
    (constantFiber_homogeneous 0)).sub hw |>.C_mul parameter)).add (hw.C_mul _)

/-- The actual coefficient specialization of the full invariant sextic family
over the generic pencil field. -/
def normalizedCoefficients : CycleQ2GenericSexticGradient.CoeffRing →+* K :=
  (aeval (fun e : FullInvariantIndex 6 =>
    monicNormalization.coeff (fullExponentOf e.val))).toRingHom

@[simp] theorem normalizedCoefficients_X (e : FullInvariantIndex 6) :
    normalizedCoefficients (X e) = monicNormalization.coeff (fullExponentOf e.val) :=
  aeval_X _ e

theorem universalEquation_normalized :
    CycleQ2GeometricHodgeThreefold.equation normalizedCoefficients = monicNormalization := by
  rw [CycleQ2GeometricHodgeThreefold.equation, CycleQ2GenericSexticGradient.universalF,
    map_fullInvariantPolynomial]
  refine (congrArg (fullInvariantPolynomial 6) ?_).trans
    (fullInvariantPolynomial_of_homogeneous (p := monicNormalization) (G_fullHomogeneous.C_mul _))
  funext e
  exact normalizedCoefficients_X e

theorem normalizedCoefficients_vertex :
    normalizedCoefficients CycleQ2GeometricHodgeThreefold.vertexCoefficient = 1 := by
  rw [CycleQ2GeometricHodgeThreefold.vertexCoefficient, normalizedCoefficients_X, fullSexticLeadingIndex_exponent]
  exact monicNormalization_vertexCoefficient

theorem universalEquation_ideal :
    Ideal.span {CycleQ2GeometricHodgeThreefold.equation normalizedCoefficients} =
      Ideal.span ({G} : Set P) := by
  rw [universalEquation_normalized, monicNormalization_ideal]

theorem G_homogeneous : G.IsWeightedHomogeneous geometricWeight 6 :=
  homogeneous_of_character G_fullHomogeneous

theorem G_gamma (z : K) (hz : z ^ 3 = 1) : polynomialAction z G = G := by
  simpa using polynomialAction_homogeneous z hz G 6 0 G_fullHomogeneous

/-- Vertex avoidance is preserved after every field extension of the generic field. -/
theorem no_vertex {L : Type*} [Field L] [Algebra K L] (w : L)
    (h : aeval (![0,0,0,0,w] : Fin 5 → L) G = 0) : w = 0 := by
  have hn : 1 + (algebraMap K L) parameter ^ 6 ≠ 0 := by
    simpa only [map_zero, map_one, map_add, map_pow] using
      (algebraMap K L).injective.ne vertexCoefficient_ne_zero
  simpa [G, hn] using h

attribute [local instance] MvPolynomial.weightedGradedAlgebra

abbrev QuotientRing := P ⧸ Ideal.span {G}
abbrev quotient := Ideal.Quotient.mkₐ K (Ideal.span {G} : Ideal P)

private theorem ideal_homogeneous : (Ideal.span {G}).IsHomogeneous (PolynomialGrade K) := by
  apply Ideal.homogeneous_span
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact ⟨6, G_homogeneous⟩

abbrev grade (n : ℕ) : Submodule K QuotientRing :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade (PolynomialGrade K) (Ideal.span {G}) n

instance : GradedRing grade :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing (PolynomialGrade K)
    (Ideal.span {G}) ideal_homogeneous

def hypersurface : Scheme := Proj grade

def patch (i : Fin 4) : hypersurface.Opens := Proj.basicOpen grade (quotient (X i.castSucc))

private theorem all_coordinate_opens :
    (⨆ j : Fin 5, Proj.basicOpen grade (quotient (X j))) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn x hx
  obtain ⟨p,hp,rfl⟩ := hx
  have hvars : Ideal.span (Set.range (X : Fin 5 → P)) ≤
      (Ideal.span (Set.range (fun j : Fin 5 => quotient (X j)))).comap quotient := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Ideal.subset_span ⟨j,rfl⟩
  exact hvars (CycleQ2IncidenceFamilyContainment.homogeneous_mem_variableIdeal hn hp)

theorem patch_cover : (⨆ i, patch i) = ⊤ := by
  apply top_unique
  intro x _
  let I := x.asHomogeneousIdeal.toIdeal
  letI : I.IsPrime := x.isPrime
  let L := I.ResidueField
  let f : P →+* L := (algebraMap QuotientRing L).comp quotient.toRingHom
  letI : Algebra K L := (f.comp MvPolynomial.C).toAlgebra
  have e : MvPolynomial.eval₂Hom (algebraMap K L) (fun j => f (X j)) = f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [eval₂Hom_C]
      rfl
    · intro j
      simp only [eval₂Hom_X']
  rw [Opens.mem_iSup]
  change ∃ j : Fin 4, quotient (X j.castSucc) ∉ I
  by_contra! h
  have zero (j : Fin 4) : f (X j.castSucc) = 0 := by
    exact (Ideal.algebraMap_residueField_eq_zero).mpr (h j)
  have ev : (fun j : Fin 5 => f (X j)) = ![0,0,0,0,f (X 4)] := by
    funext j
    fin_cases j <;> first | rfl | exact zero 0 | exact zero 1 | exact zero 2 | exact zero 3
  have hf : f G = 0 := by
    change algebraMap QuotientRing L (Ideal.Quotient.mk _ G) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton G)), map_zero]
  have hv : f (X 4) = 0 := by
    apply no_vertex
    change MvPolynomial.eval₂Hom (algebraMap K L) _ G = 0
    rw [← ev, e]
    exact hf
  have hx : x ∈ ⨆ j : Fin 5, Proj.basicOpen grade (quotient (X j)) := by
    rw [all_coordinate_opens]
    trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
  apply hj
  refine Fin.lastCases (motive := fun k => quotient (X k) ∈ I) ?_ (fun k => ?_) j
  · exact Ideal.algebraMap_residueField_eq_zero.mp hv
  · exact h k

def gammaCone (z : K) (hz : z^3 = 1) : QuotientRing →ₐ[K] QuotientRing :=
  Ideal.quotientMapₐ (Ideal.span {G}) (polynomialAction z) (by
    apply Ideal.span_le.mpr
    rintro p (rfl : p = G)
    change polynomialAction z G ∈ Ideal.span {G}
    rw [G_gamma z hz]
    exact Ideal.subset_span (Set.mem_singleton G))

theorem gammaCone_mk (z : K) (hz : z^3 = 1) (p : P) :
    gammaCone z hz (quotient p) = quotient (polynomialAction z p) := rfl

private theorem gamma_polynomial_cube (z : K) (hz : z^3 = 1) (p : P) :
    polynomialAction z (polynomialAction z (polynomialAction z p)) = p := by
  let f := polynomialAction z
  have he : f.comp (f.comp f) = AlgHom.id K P := by
    apply MvPolynomial.algHom_ext
    intro j
    let k : K := (![z^2,z^2,z,1,1] : Fin 5 → K) j
    have hk : k^3 = 1 := by
      have h₂ : (z^2)^3 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
      fin_cases j <;> simp [k, hz, h₂]
    have hx : f (X j) = C k * X j := by fin_cases j <;> simp [f, k, actionValues]
    have hc : (C k : P)^3 = 1 := by rw [← map_pow, hk, map_one]
    change f (f (f (X j))) = X j
    simp only [hx, map_mul, f, polynomialAction_C]
    linear_combination X j * hc
  exact AlgHom.congr_fun he p

def gammaGraded (z : K) (hz : z^3 = 1) : grade →+*ᵍ grade where
  toRingHom := (gammaCone z hz).toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    refine ⟨polynomialAction z p, ?_, rfl⟩
    change IsWeightedHomogeneous geometricWeight p n at hp
    change IsWeightedHomogeneous geometricWeight (polynomialAction z p) n
    induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simpa only [map_zero] using isWeightedHomogeneous_zero K geometricWeight n
    | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
    | monomial e c he =>
      rw [polynomialAction_monomial]
      exact (isWeightedHomogeneous_monomial geometricWeight e c he).C_mul _

theorem gamma_cube (z : K) (hz : z^3 = 1) (x : QuotientRing) :
    gammaGraded z hz (gammaGraded z hz (gammaGraded z hz x)) = x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg quotient (gamma_polynomial_cube z hz p)

def gammaProjective (z : K) (hz : z^3 = 1) : hypersurface ≅ hypersurface :=
  CycleQ2LiteralOrbitAction.cyclicProjIso (gammaGraded z hz) (gamma_cube z hz)

theorem gammaProjective_cube (z : K) (hz : z^3 = 1) :
    (gammaProjective z hz).hom ≫ (gammaProjective z hz).hom ≫ (gammaProjective z hz).hom =
      𝟙 hypersurface :=
  CycleQ2LiteralOrbitAction.cyclicProjMap_cube (gammaGraded z hz) (gamma_cube z hz)

def toGenericPoint : hypersurface ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero grade ≫ Spec.map (CommRingCat.ofHom (algebraMap K (grade 0)))

theorem gammaProjective_overGenericPoint (z : K) (hz : z^3 = 1) :
    (gammaProjective z hz).hom ≫ toGenericPoint = toGenericPoint := by
  apply CycleQ2IncidenceFamilyContainment.projectiveMap_coefficientBase
    (gammaGraded z hz) (CycleQ2LiteralOrbitAction.cyclic_irrelevant_le_map _ (gamma_cube z hz))
  ext c
  exact (gammaCone z hz).commutes c

end CycleQ2ProtectedGenericPencilModel
end

#print axioms CycleQ2ProtectedGenericPencilModel.restrictProtected_F
#print axioms CycleQ2ProtectedGenericPencilModel.patch_cover
#print axioms CycleQ2ProtectedGenericPencilModel.G_gamma

#print axioms CycleQ2ProtectedGenericPencilModel.monicNormalization_vertexCoefficient
#print axioms CycleQ2ProtectedGenericPencilModel.gammaProjective
#print axioms CycleQ2ProtectedGenericPencilModel.universalEquation_normalized
