import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Scheme

/-! The coordinate k-algebras of the actual opens of a scheme over k. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite

namespace CycleQ2.Cech.Sections

variable {k : Type} [CommRing k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))

def baseMap (W : X.Opens) : k →+* Γ(X,W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.presheaf.map W.leTop.op).hom

abbrev algebra (W : X.Opens) : Algebra k Γ(X,W) := (baseMap f W).toAlgebra

theorem restrict_baseMap {U V : X.Opensᵒᵖ} (g : U ⟶ V) (c : k) :
    X.presheaf.map g (baseMap f U.unop c) = baseMap f V.unop c := by
  change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
    X.presheaf.map U.unop.leTop.op) ≫ X.presheaf.map g) c = _
  rw [Category.assoc,Category.assoc,← X.presheaf.map_comp]
  rfl

/-- The literal restriction on the structure sheaf, bundled as a k-algebra map. -/
def restrict {U V : X.Opensᵒᵖ} (g : U ⟶ V) :
    letI := algebra f U.unop
    letI := algebra f V.unop
    Γ(X,U.unop) →ₐ[k] Γ(X,V.unop) :=
  letI := algebra f U.unop
  letI := algebra f V.unop
  { (X.presheaf.map g).hom with commutes' := restrict_baseMap f g }

/-- The k-algebra-valued structure presheaf. -/
def presheaf : X.Opensᵒᵖ ⥤ CommAlgCat.{0} k where
  obj W := letI := algebra f W.unop; CommAlgCat.of k Γ(X,W.unop)
  map g := CommAlgCat.ofHom (restrict f g)
  map_id W := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ConcreteCategory.congr_hom (X.presheaf.map_id W) x
  map_comp g h := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp g h) x

end CycleQ2.Cech.Sections
end

#print axioms CycleQ2.Cech.Sections.presheaf
