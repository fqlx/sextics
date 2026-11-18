import Proposal.ScratchLogarithmicSquare
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The de Rham cochain complex of a regular coordinate chart

The objects are the true exterior powers of the Kähler module, including degree
zero; their graded additive differential uses the prescribed basis of coordinate
differentials. Its successive maps compose to zero in every degree.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LogChartComplex
open CategoryTheory CycleQ2LogarithmicDifferential
variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable {I : Type} [Fintype I] [LinearOrder I]
variable (b : Module.Basis I R (KaehlerDifferential k R))

abbrev object (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (n : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (Form k R n)

/-- The complex vanishes in every degree above the size of the true coordinate basis. -/
theorem form_subsingleton_of_gt (n : ℕ) (hn : Fintype.card I < n) :
    Subsingleton (Form k R n) := by
  constructor
  intro α β
  apply (b.exteriorPower n).repr.injective
  ext q
  exfalso
  apply hn.not_ge
  simpa only [Set.powersetCard.card_eq] using Finset.card_le_univ (q : Finset I)

def arrow (n : ℕ) : object k R n ⟶ object k R (n+1) :=
  AddCommGrpCat.ofHom (exteriorD b n)

def complex (x : I → R) (hx : ∀ i, b i = KaehlerDifferential.D k R (x i)) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (object k R) (arrow b) (fun n => by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact exteriorD_squared b x hx n)

@[simp] theorem complex_d (x : I → R) (hx : ∀ i, b i = KaehlerDifferential.D k R (x i)) (n : ℕ) :
    (complex b x hx).d n (n+1) = AddCommGrpCat.ofHom (exteriorD b n) :=
  CochainComplex.of_d (object k R) (arrow b) n

end CycleQ2LogChartComplex
end

#print axioms CycleQ2LogChartComplex.complex
