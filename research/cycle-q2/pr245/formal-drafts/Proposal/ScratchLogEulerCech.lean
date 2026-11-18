import Proposal.ScratchLogHomogeneousCone

/-!
# Contraction of the weighted Čech representative

Euler contraction on Čech degree p is multiplied by (-1)^p, so that it
passes both the cocycle identities and the meromorphic comparison to forms
of one lower degree. The degree-zero correction of a boundary acquires a
minus sign.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogEulerCech

open CycleQ2LogarithmicDifferential CycleQ2LogHomogeneousCone
open CycleQ2LiteralThreefoldResidueContraction (interior)
variable {k R J : Type} [CommRing k] [CommRing R] [Algebra k R]
variable (b : Module.Basis (Fin 5) R (KaehlerDifferential k R))
variable (E : KaehlerDifferential k R →ₗ[R] R)
variable (v : J → Form k R 5) (e : J → J → Form k R 4) (f : J → J → J → Form k R 3)

/-- The signed horizontal images of a Cartan-invariant cone cocycle satisfy
all four Čech–de Rham closure equations. -/
theorem cocycle (i j l m : J)
    (hv : Invariant b E 4 (v i)) (he : Invariant b E 3 (e i j))
    (hf : Invariant b E 2 (f i j l))
    (heq : exteriorD b 4 (e i j) = v j-v i)
    (hfq : exteriorD b 3 (f i j l) = -(e j l-e i l+e i j))
    (hδ : f j l m-f i l m+f i j m-f i j l = 0) :
    exteriorD b 4 (interior 4 E (v i)) = 0 ∧
    exteriorD b 3 (-interior 3 E (e i j)) = interior 4 E (v j)-interior 4 E (v i) ∧
    exteriorD b 2 (interior 2 E (f i j l)) =
      -((-interior 3 E (e j l))-(-interior 3 E (e i l))+(-interior 3 E (e i j))) ∧
    interior 2 E (f j l m)-interior 2 E (f i l m)+interior 2 E (f i j m)-interior 2 E (f i j l) = 0 := by
  haveI := CycleQ2PoleReductionLocal.six_subsingleton b
  have hd : exteriorD b 5 (v i) = 0 := Subsingleton.elim _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(invariant_iff b E 4 _).mp hv, hd, map_zero, neg_zero]
  · rw [map_neg, (invariant_iff b E 3 _).mp he, heq, map_sub, neg_neg]
  · rw [(invariant_iff b E 2 _).mp hf, hfq, map_neg, map_add, map_sub, neg_neg]
    abel
  · simpa only [map_sub, map_add, map_zero] using congrArg (interior 2 E) hδ

/-- The two meromorphic corrections still exhibit the signed Euler-contracted
representative and the Euler-contracted initial form as cohomologous. -/
theorem comparison (t : Form k R 5) (u : J → Form k R 4) (q : J → J → Form k R 3)
    (i j l : J) (hu : Invariant b E 3 (u i)) (hq : Invariant b E 2 (q i j))
    (hv : v i = t-exteriorD b 4 (u i))
    (he : e i j = u i-u j+exteriorD b 3 (q i j))
    (hf : f i j l = -q j l+q i l-q i j) :
    interior 4 E (v i) = interior 4 E t - exteriorD b 3 (-interior 3 E (u i)) ∧
    -interior 3 E (e i j) = (-interior 3 E (u i))-(-interior 3 E (u j))+
      exteriorD b 2 (interior 2 E (q i j)) ∧
    interior 2 E (f i j l) = -interior 2 E (q j l)+interior 2 E (q i l)-interior 2 E (q i j) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hv, map_sub, map_neg, (invariant_iff b E 3 _).mp hu, neg_neg]
  · rw [he, map_add, map_sub, (invariant_iff b E 2 _).mp hq]
    abel
  · rw [hf, map_sub, map_add, map_neg]

end CycleQ2LogEulerCech
end

#print axioms CycleQ2LogEulerCech.cocycle
#print axioms CycleQ2LogEulerCech.comparison
