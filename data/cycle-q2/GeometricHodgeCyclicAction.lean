import Proposal.GeometricHodgeThreefold
import Proposal.GeometricLiteralThreefoldOrbitActionCharts
import Proposal.GeometricHodgeEuler

/-!
# The diagonal cyclic action on the full invariant sextic

Every specialization of the original invariant sextic is fixed by the
diagonal substitution. This gives a group action on its weighted projective
hypersurface over the coefficient field. The four normalized coordinates carry
the corresponding ratios of the five original characters.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeCyclicAction

open CategoryTheory AlgebraicGeometry MvPolynomial CycleQ2IncidenceNormalForm
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceEquations CycleQ2SeedCyclicAction
  CycleQ2GeometricHodgeThreefold CycleQ2LiteralOrbitAction CycleQ2GenericSexticGradient
  CycleQ2LiteralThreefoldOrbitAction CycleQ2IncidenceFamilyContainment
  CycleQ2HodgeEuler

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3 = 1)

include hz in
theorem invariant : polynomialAction z (equation φ) = equation φ := by
  have hg : HG (equation φ) (6,0) := by
    rw [equation, universalF, map_fullInvariantPolynomial]
    exact fullInvariantPolynomial_homogeneous _ _
  simpa using polynomialAction_homogeneous z hz (equation φ) 6 0 hg

def coneAction : cone φ →ₐ[ℂ] cone φ :=
  Ideal.quotientMapₐ (Ideal.span {equation φ}) (polynomialAction z) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change polynomialAction z (equation φ) ∈ Ideal.span {equation φ}
    rw [invariant φ z hz]
    exact Ideal.subset_span (Set.mem_singleton _))

def gradedAction : grade φ →+*ᵍ grade φ where
  toRingHom := (coneAction φ z hz).toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact ⟨polynomialAction z p, polynomialAction_weighted z hp, rfl⟩

theorem gradedAction_cube (x : cone φ) :
    gradedAction φ z hz (gradedAction φ z hz (gradedAction φ z hz x)) = x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (quotient φ) (polynomialAction_cube z hz p)

def action : threefold φ ≅ threefold φ :=
  cyclicProjIso (gradedAction φ z hz) (gradedAction_cube φ z hz)

private theorem polynomial_comp (w : ℂ) :
    (polynomialAction z).comp (polynomialAction w) = polynomialAction (z*w) := by
  apply MvPolynomial.algHom_ext
  intro i
  have h : char (z*w) i = char z i * char w i := by fin_cases i <;> simp [char, mul_pow]
  simp only [AlgHom.comp_apply, action_X, map_mul, polynomialAction_C, h]
  ring

theorem gradedAction_comp (w : ℂ) (hw : w^3=1) :
    (gradedAction φ z hz).comp (gradedAction φ w hw) =
      gradedAction φ (z*w) (cubeRoot_mul hz hw) := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (quotient φ) (AlgHom.congr_fun (polynomial_comp z w) p)

theorem action_comp (w : ℂ) (hw : w^3=1) :
    (action φ z hz).hom ≫ (action φ w hw).hom = (action φ (z*w) (cubeRoot_mul hz hw)).hom := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  simp only [gradedAction_comp]

theorem action_one : (action φ 1 (one_pow 3)).hom = 𝟙 _ := by
  apply (cancel_epi (action φ 1 (one_pow 3)).hom).mp
  simpa only [mul_one, Category.comp_id] using action_comp φ 1 (one_pow 3) 1 (one_pow 3)

theorem action_overBase : (action φ z hz).hom ≫ toBase φ = toBase φ := by
  apply projectiveMap_coefficientBase (gradedAction φ z hz) (cyclic_irrelevant_le_map _ (gradedAction_cube φ z hz))
  ext c
  exact (coneAction φ z hz).commutes c

theorem coordinateOpen_stable (i : Fin 4) : (action φ z hz).hom ⁻¹ᵁ coordinateOpen φ i = coordinateOpen φ i := by
  change (Proj.map (gradedAction φ z hz) _) ⁻¹ᵁ Proj.basicOpen _ _ = _
  rw [Proj.map_preimage_basicOpen]
  change Proj.basicOpen _ (quotient φ (polynomialAction z (X i.castSucc))) = _
  rw [action_X, map_mul, Proj.basicOpen_mul]
  have hu : IsUnit (quotient φ (C (char z i.castSucc))) :=
    (isUnit_iff_ne_zero.mpr (char_ne_zero z hz i.castSucc)).map ((quotient φ).comp C)
  have ht : Proj.basicOpen (grade φ) (quotient φ (C (char z i.castSucc))) = ⊤ := by
    apply top_unique
    rw [← Proj.basicOpen_one (grade φ)]
    exact Proj.basicOpen_mono _ _ _ hu.dvd
  rw [ht, top_inf_eq]
  rfl

def factor (i : Fin 4) (j : Fin 5) : ℂ := char z j * (baseScale z i)^geometricWeight j

def chartFactor (i j : Fin 4) : ℂ := factor z i (i.castSucc.succAbove j)

def chartPoly (i : Fin 4) : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  aeval (fun j => C (chartFactor z i j) * X j)

include hz in
theorem factor_self (i : Fin 4) : factor z i i.castSucc = 1 := by
  rw [factor, CycleQ2SeedFermatProj.geometricWeight_castSucc, pow_one, baseScale,
    mul_inv_cancel₀ (char_ne_zero z hz _)]

include hz in
theorem chartPoly_dehom (i : Fin 4) {n : ℕ} (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    chartPoly z i (dehom i p) = C (baseScale z i^n) * dehom i (polynomialAction z p) := by
  let v : Fin 5 → MvPolynomial (Fin 4) ℂ := fun j => dehom i (polynomialAction z (X j))
  let c : MvPolynomial (Fin 4) ℂ := C (baseScale z i)
  have h : (chartPoly z i).comp (dehom i) = aeval (fun j => c^geometricWeight j * v j) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
    · have hs : dehom i (C (char z i.castSucc)) = C _ := aeval_C _ _
      simp only [AlgHom.comp_apply, dehom_X_self, map_one, aeval_X, v, action_X, map_mul,
        hs, mul_one, c, CycleQ2SeedFermatProj.geometricWeight_castSucc, pow_one]
      rw [← map_mul, baseScale, inv_mul_cancel₀ (char_ne_zero z hz _), map_one]
    · have hs : dehom i (C (char z (i.castSucc.succAbove k))) = C _ := aeval_C _ _
      simp only [AlgHom.comp_apply, dehom_X_succAbove, chartPoly, aeval_X, v, action_X,
        map_mul, hs, chartFactor, factor, map_pow, c]
      ring
  have hv : (dehom i).comp (polynomialAction z) = aeval v := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, aeval_X]
  have he := CycleQ2IncidenceDehomogenizedChart.weighted_homogeneous_eval_scale C v c p n hp
  change ((chartPoly z i).comp (dehom i)) p = C (baseScale z i ^ n) * ((dehom i).comp (polynomialAction z)) p
  rw [h, hv, map_pow]
  exact he

include hz in
theorem chartPoly_F (i : Fin 4) : chartPoly z i (F φ i) = F φ i := by
  change chartPoly z i (dehom i (equation φ)) = _
  rw [chartPoly_dehom z hz i _ (equation_homogeneous φ), invariant φ z hz, baseScale_six z hz, map_one, one_mul] <;> rfl

include hz in
/-- The normalization by the sixth power of a weight-one coordinate
preserves the character of a degree-six deformation numerator. -/
theorem chartPoly_direction (i : Fin 4) (χ : ZMod 3) (p : MvPolynomial (Fin 5) ℂ)
    (hp : HG p (6,χ)) :
    chartPoly z i (dehom i p) = C (z^χ.val) * dehom i p := by
  rw [chartPoly_dehom z hz i p (homogeneous_of_character hp),
    polynomialAction_homogeneous z hz p 6 χ hp, baseScale_six z hz, map_one, one_mul,
    map_mul, show dehom i (C (z^χ.val)) = C _ from aeval_C _ _]

def chartAction (i : Fin 4) : chart φ i →ₐ[ℂ] chart φ i :=
  Ideal.quotientMapₐ (Ideal.span {F φ i}) (chartPoly z i) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change chartPoly z i (F φ i) ∈ Ideal.span {F φ i}
    rw [chartPoly_F φ z hz]
    exact Ideal.subset_span (Set.mem_singleton _))

end CycleQ2HodgeCyclicAction
end

#print axioms CycleQ2HodgeCyclicAction.action_comp
#print axioms CycleQ2HodgeCyclicAction.chartPoly_F
#print axioms CycleQ2HodgeCyclicAction.action_overBase
#print axioms CycleQ2HodgeCyclicAction.coordinateOpen_stable
#print axioms CycleQ2HodgeCyclicAction.chartPoly_direction
