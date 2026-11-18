import Proposal.GeometricHodgeInfinitesimalQuotient
import Proposal.GeometricSquareZeroProjectors

/-!
# Changes of coordinates of first-order weighted sextic equations

An infinitesimal polynomial vector field gives an automorphism of the dual
polynomial ring. It fixes the dual scalar parameter and reduces to the
identity. Two degree-six directions have the same Jacobian class exactly
when a weighted velocity carries one deformed equation to the other.
The induced isomorphism of hypersurface rings commutes with reduction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeEquationShear

open CycleQ2GeometricSurfaceFirstOrder
open CycleQ2HodgeInfinitesimalQuotient
open CycleQ2GenericSexticGradient (CoeffRing)

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- The change of variables that sends each polynomial x to x + εD(x). -/
def shear (D : Derivation K R R) : Dual R ≃ₐ[K] Dual R where
  toFun z := (z.fst, z.snd + D z.fst)
  invFun z := (z.fst, z.snd - D z.fst)
  left_inv z := by apply TrivSqZeroExt.ext <;> simp
  right_inv z := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change x.snd + y.snd + D (x.fst + y.fst) = (x.snd + D x.fst) + (y.snd + D y.fst)
      rw [map_add]
      abel
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change x.fst * y.snd + x.snd * y.fst + D (x.fst * y.fst) =
        x.fst * (y.snd + D y.fst) + (x.snd + D x.fst) * y.fst
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
  commutes' k := by
    apply TrivSqZeroExt.ext
    · rfl
    · change 0 + D (algebraMap K R k) = 0
      rw [Derivation.map_algebraMap, add_zero]

theorem shear_dualScalar (D : Derivation K R R) (a b : K) :
    shear D (algebraMap K R a, algebraMap K R b) =
      (algebraMap K R a, algebraMap K R b) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change _ + D (algebraMap K R a) = _
    rw [Derivation.map_algebraMap, add_zero]

theorem shear_relation_iff (D : Derivation K R R) (f a b : R) :
    shear D (relation f a) = relation f b ↔ D f = a - b := by
  constructor
  · intro h
    have h' : -a + D f = -b := congrArg TrivSqZeroExt.snd h
    calc
      D f = a + (-a + D f) := by abel
      _ = a - b := by rw [h', sub_eq_add_neg]
  · intro h
    apply TrivSqZeroExt.ext
    · rfl
    · change -a + D f = -b
      rw [h]
      abel

/-- An actual isomorphism between the two first-order hypersurface rings. -/
def hypersurfaceEquiv (D : Derivation K R R) (f a b : R) (h : D f = a - b) :
    Deformation f a ≃ₐ[K] Deformation f b :=
  Ideal.quotientEquivAlg _ _ (shear D) (by
    rw [deformationIdeal, deformationIdeal, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun q : Dual R => Ideal.span {q}) ((shear_relation_iff D f a b).2 h).symm)

theorem hypersurfaceEquiv_reduction (D : Derivation K R R) (f a b : R)
    (h : D f = a - b) (z : Deformation f a) :
    reduction f b (hypersurfaceEquiv D f a b h z) = reduction f a z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem hypersurfaceEquiv_epsilon (D : Derivation K R R) (f a b : R)
    (h : D f = a - b) (z : Closed f) :
    hypersurfaceEquiv D f a b h (epsilon f a z) = epsilon f b z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk (deformationIdeal f b) (shear D (TrivSqZeroExt.inr z)) =
    Ideal.Quotient.mk (deformationIdeal f b) (TrivSqZeroExt.inr z)
  congr 1
  apply TrivSqZeroExt.ext
  · rfl
  · change z + D 0 = z
    simp

section Weighted
variable {B : Type} [CommRing B]

theorem class_eq_iff_shear (φ : CoeffRing →+* B) (χ : ZMod 3) (a b : Directions B χ) :
    directionClass φ χ a = directionClass φ χ b ↔
      ∃ v : Velocities B χ, shear (velocityDerivation v) (relation (FiberPolynomial φ) a.val) =
        relation (FiberPolynomial φ) b.val := by
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_directionClass]
  constructor
  · rintro ⟨v,h⟩
    exact ⟨v, (shear_relation_iff _ _ _ _).2 (congrArg Subtype.val h)⟩
  · rintro ⟨v,h⟩
    exact ⟨v, Subtype.ext ((shear_relation_iff _ _ _ _).1 h)⟩

end Weighted
end CycleQ2HodgeEquationShear
end

#print axioms CycleQ2HodgeEquationShear.class_eq_iff_shear
#print axioms CycleQ2HodgeEquationShear.hypersurfaceEquiv_reduction
