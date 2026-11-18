import Proposal.ScratchCechSchemeSectionAlgebras

/-! Evaluation of native sections at a field-valued point. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite

namespace CycleQ2.Cech.KPoint

variable {k K : Type} [CommRing k] [Field K] [Algebra k K] {X : Scheme.{0}}
    (g : Spec (CommRingCat.of K) ⟶ X)

def point : X := g (⊥ : PrimeSpectrum K)

theorem preimage_top {W : X.Opens} (hx : point g ∈ W) : ⊤ ≤ g ⁻¹ᵁ W := by
  intro t _
  change g t ∈ W
  rw [Subsingleton.elim t (⊥ : PrimeSpectrum K)]
  exact hx

def evalRing (W : X.Opens) (hx : point g ∈ W) : Γ(X,W) →+* K :=
  (g.appLE W ⊤ (preimage_top g hx) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom

theorem evalRing_restrict {V W : X.Opens} (h : V ≤ W) (hx : point g ∈ V) :
    (evalRing g V hx).comp (X.presheaf.map (homOfLE h).op).hom = evalRing g W (h hx) := by
  change (X.presheaf.map (homOfLE h).op ≫ g.appLE V ⊤ _ ≫ _).hom = _
  rw [g.map_appLE_assoc]
  rfl

variable (f : X ⟶ Spec (CommRingCat.of k))
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)))

theorem evalRing_base (W : X.Opens) (hx : point g ∈ W) :
    (evalRing g W hx).comp (Sections.baseMap f W) = algebraMap k K := by
  have e : X.presheaf.map W.leTop.op ≫ g.appLE W ⊤ (preimage_top g hx) = g.appTop := by
    rw [g.map_appLE]
    change g.appTop ≫ (Spec (CommRingCat.of K)).presheaf.map (𝟙 _) = _
    simp
  change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.presheaf.map W.leTop.op) ≫
    g.appLE W ⊤ _ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom = _
  simp only [Category.assoc, reassoc_of% e]
  rw [← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hg, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]
  rfl

/-- Native sections evaluated in the specified field. -/
def eval (f : X ⟶ Spec (CommRingCat.of k)) (g : Spec (CommRingCat.of K) ⟶ X)
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) (W : X.Opens) (hx : point g ∈ W) :
    (Sections.presheaf f).obj (op W) →ₐ[k] K :=
  { evalRing g W hx with
    commutes' c := RingHom.congr_fun (evalRing_base g f hg W hx) c }

theorem eval_restrict {V W : X.Opens} (h : V ≤ W) (hx : point g ∈ V) :
    (eval f g hg V hx).comp (((Sections.presheaf f).map (homOfLE h).op).hom) =
      eval f g hg W (h hx) :=
  AlgHom.ext fun a => RingHom.congr_fun (evalRing_restrict g h hx) a

end CycleQ2.Cech.KPoint
end

#print axioms CycleQ2.Cech.KPoint.eval
#print axioms CycleQ2.Cech.KPoint.eval_restrict
