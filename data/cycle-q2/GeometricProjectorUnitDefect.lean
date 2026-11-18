import Proposal.GeometricFamilyDeformation
import Proposal.GeometricSquareZeroAtiyah
import Proposal.GeometricLiteralMovingDivisorChern

/-!
# Projector and transition defects on a rank-one frame

The scalar extracted from the lifted matrix projector is the first-order
coefficient of the multiplicative transition defect. Both expressions use the
product-minus-direct convention.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2ProjectorUnitDefect

open Matrix CycleQ2GeometricRankOneImage CycleQ2GeometricProjectorDefect
open scoped BigOperators Matrix

variable {E R m n I : Type*} [CommRing E] [CommRing R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A generator of the lifted image and its normalized coordinate. -/
structure Frame (e : Matrix m m E) where
  x : m → E
  y : m → E
  normalized : y ⬝ᵥ x = 1
  eq_outer : e = vecMulVec x y

def transition {e f : Matrix m m E} (a : Frame e) (b : Frame f) : E := a.y ⬝ᵥ b.x

omit [DecidableEq m] in
theorem frame_product {e f : Matrix m m E} (a : Frame e) (b : Frame f) :
    e * f = transition a b • vecMulVec a.x b.y := by
  calc
    e * f = vecMulVec a.x a.y * vecMulVec b.x b.y := congrArg₂ (· * ·) a.eq_outer b.eq_outer
    _ = _ := by simp only [vecMulVec_mul_vecMulVec, vecMulVec_smul, transition]

theorem frame_defect {e f g : Matrix m m E} (a : Frame e) (b : Frame f) (c : Frame g) :
    defect e f g =
      (transition a b * transition b c - transition a c) • vecMulVec a.x c.y := by
  have hc : vecMulVec a.x b.y * g = transition b c • vecMulVec a.x c.y := by
    calc
      _ = vecMulVec a.x b.y * vecMulVec c.x c.y := congrArg (vecMulVec a.x b.y * ·) c.eq_outer
      _ = _ := by simp only [vecMulVec_mul_vecMulVec, vecMulVec_smul, transition]
  rw [defect, frame_product a b, smul_mul_assoc, hc, smul_smul, frame_product a c, sub_smul]

/-- Cancelling the direct transition expresses the defect as the normalized
unit defect times the direct product of the two original projectors. -/
theorem frame_defect_units {e f g : Matrix m m E} (a : Frame e) (b : Frame f) (c : Frame g)
    (u v d : Eˣ) (hu : (u : E) = transition a b) (hv : (v : E) = transition b c)
    (hd : (d : E) = transition a c) :
    defect e f g = (((u * v * d⁻¹ : Eˣ) : E) - 1) • (e * g) := by
  rw [frame_defect a b c, frame_product a c, ← hu, ← hv, ← hd, smul_smul]
  congr 1
  simp [sub_mul, mul_assoc]

theorem matrixScalar_projector (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w v : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1)
    (hv : ∑ q, v q * M q.1 q.2 = 1) :
    matrixScalar M v (projectorMatrix M w) = 1 := by
  change (∑ q, v q * ((projectorMatrix M w) *ᵥ (M.col q.2)) q.1) = 1
  have h (j : n) : (projectorMatrix M w) *ᵥ M.col j = M.col j :=
    projectorMatrix_mulVec_image M hM w hw (column M j)
  simpa only [h, Matrix.col_apply] using hv

theorem scalarCochain_eq_transitionCoefficient (ρ : E →+* R) (K : Coefficients ρ)
    (M : Matrix m n R) (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : I → m × n → R) (hw : ∀ i, ∑ q, w i q * M q.1 q.2 = 1)
    (e : I → Matrix m m E) (hred : ∀ i, ρ.mapMatrix (e i) = projectorMatrix M (w i))
    (v : m × n → R) (hv : ∑ q, v q * M q.1 q.2 = 1)
    (i j k : I) (a : Frame (e i)) (b : Frame (e j)) (c : Frame (e k))
    (u u' d : Eˣ) (hu : (u : E) = transition a b) (hu' : (u' : E) = transition b c)
    (hd : (d : E) = transition a c)
    (z : R) (hz : K.epsilon z = ((u * u' * d⁻¹ : Eˣ) : E) - 1) :
    scalarCochain ρ (K.matrixCoefficients m) M hM w hw e hred v i j k = z := by
  have hP := reduced_common_image ρ M hM w hw e hred
  have h : imageCoefficient ρ (K.matrixCoefficients m) M hM w hw e hred i j k =
      z • ρ.mapMatrix (e i * e k) := by
    apply (K.matrixCoefficients m).injective
    change (K.matrixCoefficients m).epsilon ((K.matrixCoefficients m).cochain e hP i j k) = _
    rw [Coefficients.epsilon_cochain, frame_defect_units a b c u u' d hu hu' hd, ← hz]
    ext p q
    exact K.epsilon_mul z ((e i * e k) p q)
  change matrixScalar M v _ = _
  rw [h, map_smul, map_mul, hP, hred, matrixScalar_projector M hM _ v (hw k) hv,
    smul_eq_mul, mul_one]

section UnitDefect

open CycleQ2GeometricSquareZeroSplittings
variable [Algebra E R]

/-- In the coefficient convention of the universal logarithmic differential,
the scalar is precisely the existing multiplicative obstruction. -/
theorem scalarCochain_eq_unitDefect (L : R ≃ₗ[E] RingHom.ker (algebraMap E R))
    (K : Coefficients (algebraMap E R)) (hK : ∀ z, K.epsilon z = epsilon L z)
    (M : Matrix m n R) (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : I → m × n → R) (hw : ∀ i, ∑ q, w i q * M q.1 q.2 = 1)
    (e : I → Matrix m m E)
    (hred : ∀ i, (algebraMap E R).mapMatrix (e i) = projectorMatrix M (w i))
    (v : m × n → R) (hv : ∑ q, v q * M q.1 q.2 = 1)
    (i j k : I) (a : Frame (e i)) (b : Frame (e j)) (c : Frame (e k))
    (u u' d : Eˣ) (hu : (u : E) = transition a b) (hu' : (u' : E) = transition b c)
    (hd : (d : E) = transition a c)
    (h : reducedUnit (C := R) u * reducedUnit u' = reducedUnit d) :
    scalarCochain (algebraMap E R) (K.matrixCoefficients m) M hM w hw e hred v i j k =
      unitDefect L u u' d h :=
  scalarCochain_eq_transitionCoefficient _ K M hM w hw e hred v hv i j k a b c u u' d
    hu hu' hd _ ((hK _).trans (epsilon_unitDefect L u u' d h))

end UnitDefect

section Pivot

private theorem kernel_square {A B : Type*} [Ring A] [Ring B] {r : A →+* B}
    (K : Coefficients r) (x : A) (hx : r x = 0) : x * x = 0 := by
  obtain ⟨a,rfl⟩ := K.exact_kernel x hx
  exact K.epsilon_mul_epsilon a a

theorem isUnit_of_reduced_unit (ρ : E →+* R) (K : Coefficients ρ)
    (hρ : Function.Surjective ρ) (z : E) (hz : IsUnit (ρ z)) : IsUnit z := by
  obtain ⟨u, hu⟩ := hz
  obtain ⟨b, hb⟩ := hρ (↑(u⁻¹) : R)
  have hk : ρ (z*b-1) = 0 := by rw [map_sub, map_mul, map_one, ← hu, hb, u.mul_inv, sub_self]
  have hh := kernel_square K _ hk
  apply IsUnit.of_mul_eq_one (b * (2 - z*b))
  linear_combination -hh


omit [DecidableEq m] in
private theorem outer_apply {S : Type*} [CommRing S] (x y z : m → S) :
    vecMulVec x y *ᵥ z = (y ⬝ᵥ z) • x := by
  rw [vecMulVec_mulVec]
  funext i
  exact mul_comm _ _

private theorem reduced_outer (ρ : E →+* R) {e : Matrix m m E} (a : Frame e) :
    ρ.mapMatrix e = vecMulVec (ρ ∘ a.x) (ρ ∘ a.y) := by
  ext i j
  change ρ (e i j) = ρ (a.x i) * ρ (a.y j)
  rw [← map_mul]
  exact congrArg ρ (congrArg (fun T : Matrix m m E => T i j) a.eq_outer)

/-- Restrict a chosen frame along the very same ring map as its projector. -/
def Frame.map (ρ : E →+* R) {e : Matrix m m E} (a : Frame e) : Frame (ρ.mapMatrix e) where
  x := ρ ∘ a.x
  y := ρ ∘ a.y
  normalized := (ρ.map_dotProduct _ _).symm.trans ((congrArg ρ a.normalized).trans ρ.map_one)
  eq_outer := reduced_outer ρ a

theorem transition_map (ρ : E →+* R) {e f : Matrix m m E} (a : Frame e) (b : Frame f) :
    transition (Frame.map ρ a) (Frame.map ρ b) = ρ (transition a b) :=
  (ρ.map_dotProduct _ _).symm

/-- Common reduced images imply the cocycle law for the reduced transitions
of any lifted frames. -/
theorem transition_reduced_mul (ρ : E →+* R) {e f g : Matrix m m E}
    (a : Frame e) (b : Frame f) (c : Frame g)
    (hfg : ρ.mapMatrix f * ρ.mapMatrix g = ρ.mapMatrix g) :
    ρ (transition a b) * ρ (transition b c) = ρ (transition a c) := by
  have hnorm : (ρ ∘ c.y) ⬝ᵥ (ρ ∘ c.x) = 1 := by
    rw [← ρ.map_dotProduct, c.normalized, map_one]
  have hc : ρ.mapMatrix g *ᵥ (ρ ∘ c.x) = ρ ∘ c.x := by
    rw [reduced_outer ρ c, outer_apply, hnorm, one_smul]
  have hf : ρ.mapMatrix f *ᵥ (ρ ∘ c.x) = ρ ∘ c.x := by
    calc
      _ = ρ.mapMatrix f *ᵥ (ρ.mapMatrix g *ᵥ (ρ ∘ c.x)) := congrArg _ hc.symm
      _ = _ := by rw [mulVec_mulVec, hfg, hc]
  rw [reduced_outer ρ b, outer_apply] at hf
  have h := congrArg (dotProduct (ρ ∘ a.y)) hf
  rw [dotProduct_smul, smul_eq_mul, ← ρ.map_dotProduct, ← ρ.map_dotProduct,
    ← ρ.map_dotProduct, mul_comm] at h
  exact h

/-- Every transition pairing of two frames with the same reduced image is a
unit in the square-zero thickening. -/
theorem isUnit_transition (ρ : E →+* R) (K : Coefficients ρ) (hρ : Function.Surjective ρ)
    {e f : Matrix m m E} (a : Frame e) (b : Frame f)
    (hfe : ρ.mapMatrix f * ρ.mapMatrix e = ρ.mapMatrix e) : IsUnit (transition a b) := by
  apply isUnit_of_reduced_unit ρ K hρ
  apply IsUnit.of_mul_eq_one (ρ (transition b a))
  exact (transition_reduced_mul ρ a b a hfe).trans ((congrArg ρ a.normalized).trans ρ.map_one)


/-- For arbitrary chosen lifted projectors and frames, the three pairings
are units and their normalized defect has exactly the original cochain as
its epsilon coefficient. -/
theorem exists_transition_units_scalarCochain (ρ : E →+* R) (K : Coefficients ρ)
    (hρ : Function.Surjective ρ)
    (M : Matrix m n R) (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : I → m × n → R) (hw : ∀ i, ∑ q, w i q * M q.1 q.2 = 1)
    (e : I → Matrix m m E) (hred : ∀ i, ρ.mapMatrix (e i) = projectorMatrix M (w i))
    (v : m × n → R) (hv : ∑ q, v q * M q.1 q.2 = 1)
    (i j k : I) (a : Frame (e i)) (b : Frame (e j)) (c : Frame (e k)) :
    ∃ u u' d : Eˣ, (u : E) = transition a b ∧ (u' : E) = transition b c ∧
      (d : E) = transition a c ∧
      K.epsilon (scalarCochain ρ (K.matrixCoefficients m) M hM w hw e hred v i j k) =
        ((u * u' * d⁻¹ : Eˣ) : E) - 1 := by
  have hP := reduced_common_image ρ M hM w hw e hred
  obtain ⟨u, hu⟩ := isUnit_transition ρ K hρ a b (hP j i)
  obtain ⟨u', hu'⟩ := isUnit_transition ρ K hρ b c (hP k j)
  obtain ⟨d, hd⟩ := isUnit_transition ρ K hρ a c (hP k i)
  have hmul : ρ (u : E) * ρ (u' : E) = ρ (d : E) := by
    rw [hu, hu', hd]
    exact transition_reduced_mul ρ a b c (hP j k)
  have hz : ρ (((u * u' * d⁻¹ : Eˣ) : E) - 1) = 0 := by
    simp only [Units.val_mul, map_sub, map_mul, map_one, hmul]
    rw [← map_mul, d.mul_inv, map_one, sub_self]
  obtain ⟨z, hz'⟩ := K.exact_kernel _ hz
  refine ⟨u, u', d, hu, hu', hd, ?_⟩
  rw [scalarCochain_eq_transitionCoefficient ρ K M hM w hw e hred v hv i j k a b c
    u u' d hu hu' hd z hz', hz']
/-- Lifting a generator on a pivot works for any idempotent lift of the given
image projector. The output generator reduces to the original column. -/
theorem exists_frame_of_pivot (ρ : E →+* R) (K : Coefficients ρ)
    (hρ : Function.Surjective ρ) (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) (p : m × n)
    (u : Rˣ) (hu : (u : R) = M p.1 p.2)
    (e : Matrix m m E) (he : e * e = e) (hred : ρ.mapMatrix e = projectorMatrix M w) :
    ∃ f : Frame e, ρ ∘ f.x = M.col p.2 ∧
      ρ ∘ f.y = (↑(u⁻¹) : R) • (projectorMatrix M w).row p.1 := by
  let P := projectorMatrix M w
  have hfix (j : n) : P *ᵥ M.col j = M.col j :=
    projectorMatrix_mulVec_image M hM w hw (column M j)
  choose t ht using fun i => hρ (M i p.2)
  let x := e *ᵥ t
  have hx : e *ᵥ x = x := by dsimp [x]; rw [mulVec_mulVec, he]
  have htx : ρ ∘ t = M.col p.2 := funext ht
  have hxr : ρ ∘ x = M.col p.2 := by
    funext i
    change ρ ((e *ᵥ t) i) = _
    rw [ρ.map_mulVec, htx]
    change (ρ.mapMatrix e *ᵥ M.col p.2) i = _
    rw [hred]
    exact congrFun (hfix p.2) i
  have hrp : ρ (x p.1) = ↑u := (congrFun hxr p.1).trans hu.symm
  obtain ⟨v, hv⟩ := isUnit_of_reduced_unit ρ K hρ (x p.1) (by rw [hrp]; exact u.isUnit)
  have hvred : Units.map ρ.toMonoidHom v = u := Units.ext ((congrArg ρ hv).trans hrp)
  have hvir : ρ (↑(v⁻¹) : E) = ↑(u⁻¹) := congrArg Units.val
    ((map_inv (Units.map ρ.toMonoidHom) v).trans (congrArg Inv.inv hvred))
  let y := (↑(v⁻¹) : E) • e.row p.1
  have hy : y ᵥ* e = y := by
    dsimp only [y]
    rw [smul_vecMul]
    exact congrArg _ (congrArg (fun A : Matrix m m E => A.row p.1) he)
  have hn : y ⬝ᵥ x = 1 := by
    dsimp only [y]
    rw [smul_dotProduct, smul_eq_mul]
    change (↑(v⁻¹) : E) * (e *ᵥ x) p.1 = 1
    rw [hx, ← hv, v.inv_mul]
  have hyr : ρ ∘ y = (↑(u⁻¹) : R) • P.row p.1 := by
    funext k
    change ρ ((↑(v⁻¹) : E) * e p.1 k) = ↑(u⁻¹) * P p.1 k
    rw [map_mul, hvir]
    exact congrArg _ (congrArg (fun A : Matrix m m R => A p.1 k) hred)
  have hr : ρ.mapMatrix (vecMulVec x y) = P := by
    ext i k
    change ρ (x i * y k) = P i k
    rw [map_mul, show ρ (x i) = M i p.2 from congrFun hxr i,
      show ρ (y k) = ↑(u⁻¹) * P p.1 k from congrFun hyr k]
    simp only [P, projectorMatrix_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = w (k,j) * ↑(u⁻¹) * (M i p.2 * M p.1 j) := by ring
      _ = _ := by rw [hM i p.2 p.1 j, ← hu]; simp [mul_assoc]
  let T := vecMulVec x y
  have hl : e * T = T := by dsimp [T]; rw [mul_vecMulVec, hx]
  have ht' : T * e = T := by dsimp [T]; rw [vecMulVec_mul, hy]
  have hT : T * T = T := by dsimp [T]; rw [vecMulVec_mul_vecMulVec, hn, one_smul]
  have hnil := kernel_square (K.matrixCoefficients m) (e-T)
    (by rw [map_sub, hred, show ρ.mapMatrix T = P from hr]; exact sub_self _)
  have hz : e - T = 0 := by
    rw [sub_mul, mul_sub, mul_sub, he, hl, ht', hT, sub_self, sub_zero] at hnil
    exact hnil
  exact ⟨⟨x,y,hn,sub_eq_zero.mp hz⟩, hxr, hyr⟩

/-- Reduction of the transition recovers the original pivot-column ratio. -/
theorem transition_reduction_of_pivots (ρ : E →+* R) (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) (p : m × n) (q : n) (u : Rˣ)
    {e f : Matrix m m E} (a : Frame e) (b : Frame f)
    (hy : ρ ∘ a.y = (↑(u⁻¹) : R) • (projectorMatrix M w).row p.1)
    (hx : ρ ∘ b.x = M.col q) :
    ρ (transition a b) = (↑(u⁻¹) : R) * M p.1 q := by
  rw [transition, ρ.map_dotProduct, hx, hy, smul_dotProduct]
  exact congrArg _ (congrFun (projectorMatrix_mulVec_image M hM w hw (column M q)) p.1)

open CategoryTheory AlgebraicGeometry CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionDivisorTransitions

/-- Every lifted idempotent over an actual framed seed section admits a
frame lifting exactly its original distinguished matrix column. -/
theorem exists_frame_on_pivot_section {V : Surface.Opens} (a : FrameData V)
    (ρ : E →+* Γ(Surface,V)) (K : Coefficients ρ) (hρ : Function.Surjective ρ)
    (w : Fin 3 × Fin 3 → Γ(Surface,V))
    (hw : ∑ q, w q * sectionMatrix a.chart V a.within q.1 q.2 = 1)
    (e : Matrix (Fin 3) (Fin 3) E) (he : e * e = e)
    (hred : ρ.mapMatrix e = projectorMatrix (sectionMatrix a.chart V a.within) w) :
    ∃ f : Frame e, ρ ∘ f.x = (sectionMatrix a.chart V a.within).col a.pivot.2 ∧
      ρ ∘ f.y = (↑(a.pivotUnit⁻¹) : Γ(Surface,V)) •
        (projectorMatrix (sectionMatrix a.chart V a.within) w).row a.pivot.1 := by
  apply exists_frame_of_pivot ρ K hρ _ _ w hw a.pivot a.pivotUnit a.pivot_eq e he hred
  intro i j k l
  exact (CycleQ2SegreLocal.minors_of_cofactors_zero _ (sectionMatrix_cofactors a) i j k l).trans
    (mul_comm _ _)

open CycleQ2LiteralMovingDivisorChern CycleQ2SeedSectionAffineInjective

/-- The change between raw pivot columns, with both columns written in the
first coordinate chart. -/
def columnTransition {V : Surface.Opens} (f g : FrameData V) : Γ(Surface,V)ˣ :=
  (pivotTransition f g)⁻¹ * secondPivot f g * f.pivotUnit⁻¹

theorem columnTransition_val {V : Surface.Opens} (f g : FrameData V) :
    (columnTransition f g : Γ(Surface,V)) =
      sectionMatrix f.chart V f.within f.pivot.1 g.pivot.2 * ↑(f.pivotUnit⁻¹) := by
  change ((sectionMatrix f.chart V f.within f.pivot.1 g.pivot.2 *
    ↑((secondPivot f g)⁻¹)) * ↑(secondPivot f g)) * ↑(f.pivotUnit⁻¹) = _
  rw [mul_assoc _ _ (↑(secondPivot f g) : Γ(Surface,V)), Units.inv_mul, mul_one]

/-- The moving ideal uses the unnormalized row in each chart. Its transition
becomes the original column transition by the coboundary of the pivot units. -/
theorem columnTransition_eq_movingSystem {V : Surface.Opens}
    (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (f g : FrameData V) :
    columnTransition f g = (movingSystem t ht).value f g * g.pivotUnit * f.pivotUnit⁻¹ := by
  change columnTransition f g = (movingUnit t ht f g)⁻¹ * g.pivotUnit * f.pivotUnit⁻¹
  rw [movingUnit_eq, divisorTransition, _root_.mul_inv_rev]
  simp only [columnTransition, secondPivot, inv_pow, mul_assoc]

/-- The transition between the lifted column frames reduces to the named
moving-divisor transition with its pivot coboundary. -/
theorem transition_reduction_movingSystem {V : Surface.Opens} (t : Fin 3 → ℂ)
    (ht : ∀ i, ChartRegular t i) (f g : FrameData V)
    (ρ : E →+* Γ(Surface,V)) (w : Fin 3 × Fin 3 → Γ(Surface,V))
    (hw : ∑ q, w q * sectionMatrix f.chart V f.within q.1 q.2 = 1)
    {e e' : Matrix (Fin 3) (Fin 3) E} (a : Frame e) (b : Frame e')
    (hy : ρ ∘ a.y = (↑(f.pivotUnit⁻¹) : Γ(Surface,V)) •
      (projectorMatrix (sectionMatrix f.chart V f.within) w).row f.pivot.1)
    (hx : ρ ∘ b.x = (sectionMatrix f.chart V f.within).col g.pivot.2) :
    ρ (transition a b) =
      (((movingSystem t ht).value f g * g.pivotUnit * f.pivotUnit⁻¹ : Γ(Surface,V)ˣ) : Γ(Surface,V)) := by
  rw [← columnTransition_eq_movingSystem t ht f g, columnTransition_val, mul_comm]
  exact transition_reduction_of_pivots ρ _ (fun i j k l =>
    (CycleQ2SegreLocal.minors_of_cofactors_zero _ (sectionMatrix_cofactors f) i j k l).trans
      (mul_comm _ _)) w hw f.pivot g.pivot.2 f.pivotUnit a b hy hx

/-- Using the raw column of the second chart before changing its coordinate
frame contributes the fourteenth power of the coordinate transition. -/
theorem transition_reduction_own_charts {V : Surface.Opens} (t : Fin 3 → ℂ)
    (ht : ∀ i, ChartRegular t i) (f g : FrameData V)
    (ρ : E →+* Γ(Surface,V)) (w : Fin 3 × Fin 3 → Γ(Surface,V))
    (hw : ∑ q, w q * sectionMatrix f.chart V f.within q.1 q.2 = 1)
    {e e' : Matrix (Fin 3) (Fin 3) E} (a : Frame e) (b : Frame e')
    (hy : ρ ∘ a.y = (↑(f.pivotUnit⁻¹) : Γ(Surface,V)) •
      (projectorMatrix (sectionMatrix f.chart V f.within) w).row f.pivot.1)
    (hx : ρ ∘ b.x = (sectionMatrix g.chart V g.within).col g.pivot.2) :
    ρ (transition a b) =
      (transitionUnit f.chart g.chart V f.within g.within : Γ(Surface,V)) ^ 14 *
      (((movingSystem t ht).value f g * g.pivotUnit * f.pivotUnit⁻¹ : Γ(Surface,V)ˣ) : Γ(Surface,V)) := by
  let M := sectionMatrix f.chart V f.within
  let c := (transitionUnit f.chart g.chart V f.within g.within : Γ(Surface,V)) ^ 14
  have hx' : ρ ∘ b.x = c • M.col g.pivot.2 :=
    hx.trans (congrArg (fun A : Matrix (Fin 3) (Fin 3) Γ(Surface,V) => A.col g.pivot.2)
      (sectionMatrix_change f.chart g.chart V f.within g.within))
  rw [transition, ρ.map_dotProduct, hx', dotProduct_smul, smul_eq_mul,
    ← columnTransition_eq_movingSystem t ht f g, columnTransition_val, hy, smul_dotProduct,
    smul_eq_mul]
  have hM (i j k l) : M i j * M k l = M k j * M i l :=
    (CycleQ2SegreLocal.minors_of_cofactors_zero M (sectionMatrix_cofactors f) i j k l).trans
      (mul_comm _ _)
  have h : (projectorMatrix M w).row f.pivot.1 ⬝ᵥ M.col g.pivot.2 = M f.pivot.1 g.pivot.2 :=
    congrFun (projectorMatrix_mulVec_image M hM w hw (column M g.pivot.2)) f.pivot.1
  change c * (_ * ((projectorMatrix M w).row f.pivot.1 ⬝ᵥ M.col g.pivot.2)) = _
  rw [h, mul_comm (↑(f.pivotUnit⁻¹) : Γ(Surface,V))]

end Pivot

end CycleQ2ProjectorUnitDefect

end

#print axioms CycleQ2ProjectorUnitDefect.scalarCochain_eq_unitDefect

#print axioms CycleQ2ProjectorUnitDefect.exists_frame_of_pivot
#print axioms CycleQ2ProjectorUnitDefect.transition_reduction_of_pivots

#print axioms CycleQ2ProjectorUnitDefect.exists_frame_on_pivot_section

#print axioms CycleQ2ProjectorUnitDefect.exists_transition_units_scalarCochain

#print axioms CycleQ2ProjectorUnitDefect.transition_reduction_movingSystem

#print axioms CycleQ2ProjectorUnitDefect.transition_reduction_own_charts
