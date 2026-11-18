import Proposal.GeometricLiteralAbelJacobiContraction
import Proposal.GeometricIncidenceFamilyContainment
import Mathlib.RingTheory.AdjoinRoot

/-!
# Regularity of the literal seed cubic on its sextic threefold

Separating the weight-two coordinate presents the cone and its four weight-one charts
as quotients by monic cubics. The surface equation comes from the coefficient ring of
this presentation. Its evaluation at the four weight-one coordinates equal to one is
nonzero, so scalar multiplication is injective on the free cubic quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

noncomputable section

namespace CycleQ2LiteralAmbientCubicRegular

open MvPolynomial CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceFamilyContainment
  CycleQ2IncidenceChartSeedFiber CycleQ2IncidenceDehomogenizedChart
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction

private abbrev seed := seedPoint (57 : ℂ) Complex.I

private def cubicBase {B : Type} [CommRing B] [Algebra ℂ B] (x : Fin 4 → B) : B :=
  (x 3 ^ 3 + x 2 ^ 3 + x 1 * x 2 * x 3 + x 0 * x 2 * x 3 + x 0 * x 1 ^ 2 + x 0 ^ 3)
    - algebraMap ℂ B Complex.I * (x 1 ^ 3 + x 3 ^ 3)

private theorem cubicBase_ne_zero {B : Type} [CommRing B] [Algebra ℂ B] (x : Fin 4 → B)
    (v : B →ₐ[ℂ] ℂ) (hv : ∀ j, v (x j) = 1) : cubicBase x ≠ 0 := by
  intro hz
  have he := congrArg v hz
  simp only [cubicBase, map_sub, map_add, map_pow, map_mul, hv, AlgHom.commutes,
    map_zero, Algebra.algebraMap_self_apply] at he
  have := congrArg Complex.re he
  norm_num at this

private theorem seed_regular {A B : Type} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra ℂ A] [Algebra ℂ B]
    (g : Poly ℂ →ₐ[ℂ] A) (e : A ≃ₐ[ℂ] Polynomial B) (x : Fin 4 → B)
    (s : B) (hx : ∀ j : Fin 4, e (g (X j.castSucc)) = Polynomial.C (x j))
    (hw : e (g (X (Fin.last 4))) = Polynomial.X - Polynomial.C s)
    (hn : cubicBase x ≠ 0) :
    Ideal.Quotient.mk (Ideal.span {g (pointEquationF seed)}) (g (pointEquationH seed)) ∈
      nonZeroDivisors (A ⧸ Ideal.span {g (pointEquationF seed)}) := by
  let E := e.toAlgHom.comp g
  have hX (j : Fin 4) : E (X j.castSucc) = Polynomial.C (x j) := hx j
  have hW : E (X (4 : Fin 5)) = Polynomial.X - Polynomial.C s := hw
  have hC (a : ℂ) : E (C a) = Polynomial.C (algebraMap ℂ B a) := E.commutes a
  have hCubic : E (smoothH Complex.I) = Polynomial.C (cubicBase x) := by
    simp only [smoothH, smoothA, smoothB, cubicBase, map_add, map_sub, map_mul, map_pow, hC]
    simp only [show (0 : Fin 5) = (0 : Fin 4).castSucc by rfl,
      show (1 : Fin 5) = (1 : Fin 4).castSucc by rfl,
      show (2 : Fin 5) = (2 : Fin 4).castSucc by rfl,
      show (3 : Fin 5) = (3 : Fin 4).castSucc by rfl, hX]
  let tail : B := x 0^6 - (57 : B)^3 * x 1^3 * x 3^3 + x 2^6 +
    cubicBase x * ((x 3^3 + x 2^3 + x 1*x 2*x 3 + x 0*x 2*x 3 + x 0*x 1^2 + x 0^3) +
      algebraMap ℂ B Complex.I * (x 1^3 + x 3^3))
  have hF : E (pointEquationF seed) = (Polynomial.X - Polynomial.C s)^3 + Polynomial.C tail := by
    rw [literal_pointEquationF, smoothF, map_add, map_mul, hCubic, seedG, CycleQ2SegreSeed.seedG_expanded]
    simp only [tail, smoothK, smoothB, smoothA, map_add, map_sub, map_mul, map_pow, hC,
      hW, map_ofNat, show (0 : Fin 5) = (0 : Fin 4).castSucc by rfl,
      show (1 : Fin 5) = (1 : Fin 4).castSucc by rfl,
      show (2 : Fin 5) = (2 : Fin 4).castSucc by rfl,
      show (3 : Fin 5) = (3 : Fin 4).castSucc by rfl, hX]
    ring
  let F := E (pointEquationF seed)
  have hmonic : F.Monic := by
    change (E (pointEquationF seed)).Monic
    rw [hF]
    apply ((Polynomial.monic_X_sub_C s).pow 3).add_of_left
    apply Polynomial.degree_C_le.trans_lt
    rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
    norm_num
  letI : Module.Free B (AdjoinRoot F) := hmonic.free_adjoinRoot
  let q : (A ⧸ Ideal.span {g (pointEquationF seed)}) ≃+* AdjoinRoot F :=
    Ideal.quotientEquiv _ _ e.toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      rfl)
  have hq : q (Ideal.Quotient.mk _ (g (pointEquationH seed))) =
      algebraMap B (AdjoinRoot F) (cubicBase x) := by
    change AdjoinRoot.mk F (E (pointEquationH seed)) = _
    rw [literal_pointEquationH, hCubic]
    rfl
  apply mem_nonZeroDivisors_iff_left.mpr
  intro z hz
  apply q.injective
  rw [map_zero]
  apply (IsRegular.of_ne_zero hn).smul_eq_zero_iff_right.mp
  rw [Algebra.smul_def, ← hq, ← map_mul, hz, map_zero]

private def coneEquiv : Poly ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 4) ℂ) :=
  (renameEquiv ℂ (finRotate 5)).trans (MvPolynomial.finSuccEquiv ℂ 4)

/-- The actual homogeneous cubic is a nonzerodivisor on the native sextic cone. -/
theorem cone_regular :
    Ideal.Quotient.mk (sexticIdeal seed) (pointEquationH seed) ∈ nonZeroDivisors (SexticRing seed) := by
  apply seed_regular (AlgHom.id ℂ _) coneEquiv (fun j => X j) 0
  · intro j
    change MvPolynomial.finSuccEquiv ℂ 4 (rename (finRotate 5) (X j.castSucc)) = _
    rw [rename_X, show finRotate 5 j.castSucc = j.succ from finRotate_of_lt j.isLt,
      finSuccEquiv_X_succ]
  · change MvPolynomial.finSuccEquiv ℂ 4 (rename (finRotate 5) (X (Fin.last 4))) = _
    rw [rename_X, finRotate_last, finSuccEquiv_X_zero, map_zero, sub_zero]
  · exact cubicBase_ne_zero _ (aeval (fun _ => (1 : ℂ))) (fun j => aeval_X _ j)

private def affineX (i : Fin 4) : Fin 4 → MvPolynomial (Fin 3) ℂ := i.insertNth 1 X

/-- Multiplication by the dehomogenized cubic is injective in each shifted affine
chart used for the ambient volume and the surface residue. -/
theorem chart_regular (i : Fin 4) : cubicOnT i ∈ nonZeroDivisors (T i) := by
  have hlin (j : Fin 4) : optionEquivLeft ℂ (Fin 3) (linearCoordinate i j) =
      Polynomial.C (affineX i j) := by
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp [affineX]
    · simp [affineX, optionEquivLeft_X_some]
  apply seed_regular (dehomogenize i) (optionEquivLeft ℂ (Fin 3)) (affineX i) (affineX i 2 ^ 2)
  · intro j
    rw [dehomogenize_castSucc, hlin]
  · rw [dehomogenize_last, map_sub, map_pow, optionEquivLeft_X_none, hlin, map_pow]
  · apply cubicBase_ne_zero _ (aeval (fun _ => (1 : ℂ)))
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩ <;> simp [affineX]

end CycleQ2LiteralAmbientCubicRegular

#print axioms CycleQ2LiteralAmbientCubicRegular.cone_regular
#print axioms CycleQ2LiteralAmbientCubicRegular.chart_regular
