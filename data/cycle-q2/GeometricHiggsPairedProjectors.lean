import Proposal.GeometricHiggsCommutantOpen
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Paired graded projectors on the two Jacobian components

A self-adjoint endomorphism preserving both graded components has adjoint
diagonal blocks. Commutation with the Higgs maps forces the upper block to
satisfy the matrix equations for the trace forms. Separation of the lower
component then determines the lower block from the upper block.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2HiggsPairedProjectors

open CycleQ2GeometricHiggsCommutantOpen

variable {K U L T : Type*} [CommRing K]
  [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]

def pairing (J : U →ₗ[K] L →ₗ[K] K) (x y : U × L) : K :=
  J x.1 y.2 - J y.1 x.2

def totalHiggs (d : U →ₗ[K] L) : Module.End K (U × L) :=
  (LinearMap.inr K U L).comp (d.comp (LinearMap.fst K U L))

def PreservesGrading (E : Module.End K (U × L)) : Prop :=
  (∀ u : U, (E (u, 0)).2 = 0) ∧ ∀ l : L, (E (0, l)).1 = 0

def upperBlock (E : Module.End K (U × L)) : Module.End K U :=
  (LinearMap.fst K U L).comp (E.comp (LinearMap.inl K U L))

def lowerBlock (E : Module.End K (U × L)) : Module.End K L :=
  (LinearMap.snd K U L).comp (E.comp (LinearMap.inr K U L))

theorem eq_blocks (E : Module.End K (U × L)) (hg : PreservesGrading E) :
    E = (upperBlock E).prodMap (lowerBlock E) := by
  apply LinearMap.ext
  rintro ⟨u, l⟩
  calc E (u, l) = E (u, 0) + E (0, l) := by
         rw [← map_add]; simp
       _ = _ := Prod.ext (by change _ + (E (0, l)).1 = _; rw [hg.2 l, add_zero]; rfl)
         (by change (E (u, 0)).2 + _ = _; rw [hg.1 u, zero_add]; rfl)

theorem blocks_adjoint (J : U →ₗ[K] L →ₗ[K] K) (E : Module.End K (U × L))
    (hself : ∀ x y, pairing J (E x) y = pairing J x (E y)) (u : U) (l : L) :
    J (upperBlock E u) l = J u (lowerBlock E l) := by
  have hh := hself (u, 0) (0, l)
  change J (E (u, 0)).1 l = J u (E (0, l)).2
  simpa only [pairing, map_zero, LinearMap.zero_apply, sub_zero] using hh

theorem blocks_commute (d : U →ₗ[K] L) (E : Module.End K (U × L))
    (hcomm : E * totalHiggs d = totalHiggs d * E) (u : U) :
    lowerBlock E (d u) = d (upperBlock E u) :=
  congrArg (fun f : Module.End K (U × L) => (f (u, 0)).2) hcomm

def tuple (b : Module.Basis (Fin 33) K U) (J : U →ₗ[K] L →ₗ[K] K)
    (D : T → U →ₗ[K] L) (sample : Fin 35 → T) : Tuple K :=
  fun m => LinearMap.BilinForm.toMatrix b (J.compl₂ (D (sample m)))

@[simp] theorem tuple_apply (b : Module.Basis (Fin 33) K U) (J : U →ₗ[K] L →ₗ[K] K)
    (D : T → U →ₗ[K] L) (sample : Fin 35 → T) (m : Fin 35) (i j : Fin 33) :
    tuple b J D sample m i j = J (b i) (D (sample m) (b j)) :=
  LinearMap.BilinForm.toMatrix_apply b _ i j

theorem upper_matrix_equation (b : Module.Basis (Fin 33) K U) (J : U →ₗ[K] L →ₗ[K] K)
    (D : T → U →ₗ[K] L) (sample : Fin 35 → T) (E : Module.End K (U × L))
    (hself : ∀ x y, pairing J (E x) y = pairing J x (E y))
    (hcomm : ∀ t, E * totalHiggs (D t) = totalHiggs (D t) * E) (m : Fin 35) :
    (LinearMap.toMatrix b b (upperBlock E)).transpose * tuple b J D sample m =
      tuple b J D sample m * LinearMap.toMatrix b b (upperBlock E) := by
  let B : LinearMap.BilinForm K U := J.compl₂ (D (sample m))
  have heq : B.compLeft (upperBlock E) = B.compRight (upperBlock E) := by
    ext u v
    change J (upperBlock E u) (D (sample m) v) = J u (D (sample m) (upperBlock E v))
    rw [blocks_adjoint J E hself, blocks_commute _ E (hcomm (sample m))]
  exact ((LinearMap.BilinForm.toMatrix_compLeft b B _).symm.trans
    (congrArg (LinearMap.BilinForm.toMatrix b) heq)).trans
      (LinearMap.BilinForm.toMatrix_compRight b B _)

/-- A scalar commutant for the trace matrices forces a single scalar on both graded pieces. -/
theorem compatible_scalar (b : Module.Basis (Fin 33) K U) (J : U →ₗ[K] L →ₗ[K] K)
    (D : T → U →ₗ[K] L) (sample : Fin 35 → T) (hsep : Function.Injective J.flip)
    (hscalar : ∀ P : Matrix (Fin 33) (Fin 33) K,
      (∀ m, P.transpose * tuple b J D sample m = tuple b J D sample m * P) →
        ∃ c : K, P = c • 1)
    (E : Module.End K (U × L)) (hgrading : PreservesGrading E)
    (hself : ∀ x y, pairing J (E x) y = pairing J x (E y))
    (hcommute : ∀ t, E * totalHiggs (D t) = totalHiggs (D t) * E) :
    ∃ c : K, E = c • 1 := by
  obtain ⟨c, hc⟩ := hscalar _ (upper_matrix_equation b J D sample E hself hcommute)
  have hu : upperBlock E = c • 1 := by
    apply (LinearMap.toMatrix b b).injective
    simpa only [map_smul, LinearMap.toMatrix_one] using hc
  have hl : lowerBlock E = c • 1 := by
    ext l
    apply hsep
    ext u
    change J u (lowerBlock E l) = J u (c • l)
    rw [← blocks_adjoint J E hself, hu]
    simp
  exact ⟨c, by rw [eq_blocks E hgrading, hu, hl]; rfl⟩

theorem compatible_scalar_of_minor_isUnit (b : Module.Basis (Fin 33) K U)
    (J : U →ₗ[K] L →ₗ[K] K) (D : T → U →ₗ[K] L) (sample : Fin 35 → T)
    (hsep : Function.Injective J.flip) (hminor : IsUnit (minor (tuple b J D sample)))
    (E : Module.End K (U × L)) (hgrading : PreservesGrading E)
    (hself : ∀ x y, pairing J (E x) y = pairing J x (E y))
    (hcommute : ∀ t, E * totalHiggs (D t) = totalHiggs (D t) * E) :
    ∃ c : K, E = c • 1 :=
  compatible_scalar b J D sample hsep (scalar_of_minor_isUnit _ hminor) E hgrading hself hcommute

theorem scalar_projector [IsDomain K] (b : Module.Basis (Fin 33) K U)
    (E : Module.End K (U × L)) (hc : ∃ c : K, E = c • 1) (hidem : E * E = E) :
    E = 0 ∨ E = 1 := by
  obtain ⟨c, rfl⟩ := hc
  have h := congrArg (fun f : Module.End K (U × L) => b.coord 0 (f (b 0, 0)).1) hidem
  change b.coord 0 (c • (c • b 0)) = b.coord 0 (c • b 0) at h
  have hc' : c * c = c := by
    simpa only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one] using h
  rcases mul_eq_zero.mp (show c * (c - 1) = 0 by rw [mul_sub, hc', mul_one, sub_self]) with hz | ho
  · simp [hz]
  · simp [sub_eq_zero.mp ho]

theorem compatible_projector_trivial_of_minor_isUnit [IsDomain K]
    (b : Module.Basis (Fin 33) K U) (J : U →ₗ[K] L →ₗ[K] K)
    (D : T → U →ₗ[K] L) (sample : Fin 35 → T) (hsep : Function.Injective J.flip)
    (hminor : IsUnit (minor (tuple b J D sample))) (E : Module.End K (U × L))
    (hgrading : PreservesGrading E)
    (hself : ∀ x y, pairing J (E x) y = pairing J x (E y))
    (hcommute : ∀ t, E * totalHiggs (D t) = totalHiggs (D t) * E)
    (hidem : E * E = E) : E = 0 ∨ E = 1 :=
  scalar_projector b E
    (compatible_scalar_of_minor_isUnit b J D sample hsep hminor E hgrading hself hcommute) hidem

end CycleQ2HiggsPairedProjectors
end

#print axioms CycleQ2HiggsPairedProjectors.compatible_projector_trivial_of_minor_isUnit
