import Proposal.ScratchLogWedge

/-!
# Exterior pullback under a rank-one change of the coordinate differentials

If two pullbacks of one-forms differ by a fixed one-form times the evaluation
of a covector, their exterior powers differ by exterior multiplication with
that one-form after insertion of the covector. They coincide on every form
annihilated by insertion. The formula holds over a semilinear scalar map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ExteriorRankOne

open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open CycleQ2LiteralThreefoldResidueContraction (interior interior_wedge)
open CycleQ2PoleReductionLocal (prepend prepend_generator contract_prepend)
open CycleQ2LogWedge (prepend_add prepend_smul prepend_swap prepend_twice)

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module S N]
variable (π : R →+* S) (F G : M →ₛₗ[π] N)

private theorem map_prepend (n : ℕ) (x : M) (η : ⋀[R]^n M) :
    exteriorMap π F (n+1) (prepend n x η) =
      prepend n (F x) (exteriorMap π F n η) := by
  have hη : η ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hη using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v,rfl⟩ := hy
    rw [prepend_generator, exteriorMap_wedge, exteriorMap_wedge, prepend_generator]
    apply congrArg (exteriorPower.ιMulti S (n+1))
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  | zero => simp only [map_zero]
  | add y z _ _ hy hz => simp only [map_add,hy,hz]
  | smul c y _ hy => simp only [map_smulₛₗ,RingHom.id_apply,hy]

private theorem split_generator (n : ℕ) (v : Fin (n+1) → M) :
    exteriorPower.ιMulti R (n+1) v =
      prepend n (v 0) (exteriorPower.ιMulti R n (Fin.tail v)) := by
  rw [prepend_generator,Fin.cons_self_tail]

private theorem generator_perturb (a : N) (l : M →ₗ[R] R)
    (h : ∀ x, G x = F x + π (l x) • a) (n : ℕ) (v : Fin (n+1) → M) :
    exteriorMap π G (n+1) (exteriorPower.ιMulti R (n+1) v) =
      exteriorMap π F (n+1) (exteriorPower.ιMulti R (n+1) v) +
        prepend n a (exteriorMap π F n (interior n l (exteriorPower.ιMulti R (n+1) v))) := by
  induction n with
  | zero =>
    let e := exteriorPower.ιMulti R 0 (Fin.tail v)
    have hι : interior 0 l (exteriorPower.ιMulti R 1 v) = l (v 0) • e := by
      rw [interior_wedge, Fin.sum_univ_one]
      simp only [Fin.val_zero,pow_zero,one_smul] <;>
        exact congrArg (l (v 0) • ·) (congrArg (exteriorPower.ιMulti R 0) (Subsingleton.elim ..))
    have he : exteriorMap π G 0 e = exteriorMap π F 0 e := by
      dsimp only [e]
      rw [exteriorMap_wedge,exteriorMap_wedge] <;>
        exact congrArg (exteriorPower.ιMulti S 0) (Subsingleton.elim ..)
    rw [hι, split_generator 0 v]
    change exteriorMap π G 1 (prepend 0 (v 0) e) =
      exteriorMap π F 1 (prepend 0 (v 0) e) +
        prepend 0 a (exteriorMap π F 0 (l (v 0) • e))
    rw [map_prepend, map_prepend, he, h, prepend_add, prepend_smul, map_smulₛₗ, map_smul]
  | succ n ih =>
    let x := v 0
    let η := exteriorPower.ιMulti R (n+1) (Fin.tail v)
    let y := exteriorMap π F n (interior n l η)
    have hη : exteriorMap π G (n+1) η = exteriorMap π F (n+1) η + prepend n a y :=
      ih (Fin.tail v)
    rw [split_generator (n+1) v]
    change exteriorMap π G (n+2) (prepend (n+1) x η) =
      exteriorMap π F (n+2) (prepend (n+1) x η) +
        prepend (n+1) a (exteriorMap π F (n+1) (interior (n+1) l (prepend (n+1) x η)))
    rw [map_prepend, map_prepend, hη, h x, contract_prepend, map_sub, map_smulₛₗ, map_prepend]
    change prepend (n+1) (F x + π (l x) • a) (exteriorMap π F (n+1) η + prepend n a y) =
      prepend (n+1) (F x) (exteriorMap π F (n+1) η) +
        prepend (n+1) a (π (l x) • exteriorMap π F (n+1) η - prepend n (F x) y)
    rw [prepend_add,prepend_smul,map_add,map_add,prepend_twice,add_zero,map_sub,map_smul,
      prepend_swap n (F x) a y] <;> abel

/-- Exterior pullback under a rank-one perturbation of a semilinear map. -/
theorem exteriorMap_perturb (a : N) (l : M →ₗ[R] R)
    (h : ∀ x, G x = F x + π (l x) • a) (n : ℕ) (ω : ⋀[R]^(n+1) M) :
    exteriorMap π G (n+1) ω = exteriorMap π F (n+1) ω +
      prepend n a (exteriorMap π F n (interior n l ω)) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    exact generator_perturb π F G a l h n v
  | zero => simp only [map_zero,add_zero]
  | add u v _ _ hu hv => simp only [map_add,hu,hv] <;> abel
  | smul c u _ hu => simp only [map_smulₛₗ,RingHom.id_apply,hu,smul_add]

theorem exteriorMap_horizontal (a : N) (l : M →ₗ[R] R)
    (h : ∀ x, G x = F x + π (l x) • a) (n : ℕ) (ω : ⋀[R]^(n+1) M)
    (hω : interior n l ω = 0) : exteriorMap π G (n+1) ω = exteriorMap π F (n+1) ω := by
  rw [exteriorMap_perturb π F G a l h n ω,hω,map_zero,map_zero,add_zero]


/-- It suffices to check the change of one-forms on coordinate differentials. -/
theorem perturb_of_basis {ι : Type} (b : Module.Basis ι R M) (a : N) (l : M →ₗ[R] R)
    (h : ∀ i, G (b i) = F (b i) + π (l (b i)) • a) (x : M) :
    G x = F x + π (l x) • a := by
  have hx : x ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i,rfl⟩ := hy; exact h i
  | zero => simp only [map_zero, zero_smul, add_zero]
  | add y z _ _ hy hz => simp only [map_add, hy, hz, add_smul] <;> abel
  | smul c y _ hy => simp only [map_smulₛₗ, RingHom.id_apply, hy, smul_add, smul_eq_mul,
      map_mul, mul_smul]

/-- The diagonal part of a rescaling on a coordinate wedge contributes
the product of the coordinate scale factors. -/
theorem exteriorMap_scaled_generator (n : ℕ) (v : Fin n → M) (w : Fin n → N) (c : Fin n → S)
    (h : ∀ i, F (v i) = c i • w i) :
    exteriorMap π F n (exteriorPower.ιMulti R n v) =
      (∏ i, c i) • exteriorPower.ιMulti S n w := by
  rw [exteriorMap_wedge]
  simp only [h, AlternatingMap.map_smul_univ]

end CycleQ2ExteriorRankOne
end

#print axioms CycleQ2ExteriorRankOne.exteriorMap_perturb
#print axioms CycleQ2ExteriorRankOne.exteriorMap_horizontal
