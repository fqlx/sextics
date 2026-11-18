import Proposal.GeometricFamilyDeformation

/-!
# A compatible image-line lift trivializes the projector obstruction

On a closed overlap the maps between lifted summands reduce to the
identity of their common marked image. Subtract a compatible map from
the product of two projectors and extract its square-zero coefficient.
The resulting edge endomorphisms have boundary equal to the obstruction
on the common image.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ProjectorCompatibleLift

open CycleQ2GeometricProjectorDefect CycleQ2GeometricRankOneImage

section Noncommutative
variable {E R I : Type*} [Ring E] [Ring R] (ρ : E →+* R) (K : Coefficients ρ)
  (e : I → E) (he : ∀ i, e i * e i = e i) (hP : ∀ i j, ρ (e i) * ρ (e j) = ρ (e j))

/-- A transition between the lifted image summands, viewed in the surrounding free module. -/
structure Lift (i j : I) where
  hom : E
  left : e i * hom = hom
  right : hom * e j = hom
  reduction : ρ hom = ρ (e j)

variable {ρ e}
def difference {i j : I} (v : Lift ρ e i j) : R :=
  K.coefficient (e i * e j - v.hom) (by rw [map_sub, map_mul, hP, v.reduction, sub_self])

theorem epsilon_difference {i j : I} (v : Lift ρ e i j) :
    K.epsilon (difference K hP v) = e i * e j - v.hom := K.epsilon_coefficient _ _

theorem difference_left {i j : I} (v : Lift ρ e i j) :
    ρ (e i) * difference K hP v = difference K hP v := by
  apply K.injective
  rw [← K.mul_epsilon, epsilon_difference, mul_sub, ← mul_assoc, he, v.left]

/-- No zero-determinant, exactness or rank argument is used in the thickened ring. -/
theorem face_difference (i j k : I) (u : Lift ρ e i j) (v : Lift ρ e j k) (w : Lift ρ e i k)
    (h : u.hom * v.hom = w.hom) :
    K.cochain e hP i j k = difference K hP v - difference K hP w + difference K hP u * ρ (e k) := by
  apply K.injective
  rw [K.epsilon_cochain, map_add, map_sub, ← v.reduction, ← K.epsilon_mul,
    epsilon_difference, epsilon_difference, epsilon_difference]
  unfold defect
  -- The expression with a right action is equivalent after the left
  -- action on the middle kernel coefficient is reduced to its image.
  have hl : e i * e j * (e j * e k - v.hom) = e j * e k - v.hom := by
    rw [← epsilon_difference K hP v, K.mul_epsilon, map_mul, hP,
      difference_left K he hP v]
  rw [mul_sub, ← mul_assoc (e i * e j), mul_assoc (e i) (e j) (e j), he] at hl
  rw [sub_mul, h]
  linear_combination (norm := abel) hl

end Noncommutative

section Matrices
variable {R E I m n : Type*} [CommRing E] [CommRing R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  (ρ : E →+* R) (K : Coefficients (ρ.mapMatrix : Matrix m m E →+* Matrix m m R))
  (M : Matrix m n R) (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
  (w : I → m × n → R) (hw : ∀ i, ∑ q, w i q * M q.1 q.2 = 1)
  (e : I → Matrix m m E) (he : ∀ i, e i * e i = e i)
  (hr : ∀ i, ρ.mapMatrix (e i) = projectorMatrix M (w i))

theorem scalar_right (C : Matrix m m R) (u : m × n → R) (k : I) :
    matrixScalar M u (C * projectorMatrix M (w k)) = matrixScalar M u C := by
  change (∑ q, u q * ((C * projectorMatrix M (w k)).mulVec (M.col q.2)) q.1) = _
  apply Finset.sum_congr rfl
  intro q _
  rw [← Matrix.mulVec_mulVec, show (projectorMatrix M (w k)).mulVec (M.col q.2) = M.col q.2 from
    projectorMatrix_mulVec_image M hM (w k) (hw k) (column M q.2)]

theorem scalar_boundary (i j k : I) (u : Lift ρ.mapMatrix e i j) (v : Lift ρ.mapMatrix e j k)
    (z : Lift ρ.mapMatrix e i k) (hc : u.hom * v.hom = z.hom) (c : m × n → R) :
    let d {a b : I} (q : Lift ρ.mapMatrix e a b) :=
      matrixScalar M c (difference K (reduced_common_image ρ M hM w hw e hr) q)
    scalarCochain ρ K M hM w hw e hr c i j k = d v - d z + d u := by
  dsimp only
  unfold scalarCochain imageCoefficient
  rw [face_difference K he _ i j k u v z hc, map_add, map_sub, hr, scalar_right M hM w hw]

end Matrices
end CycleQ2ProjectorCompatibleLift
end

#print axioms CycleQ2ProjectorCompatibleLift.scalar_boundary
