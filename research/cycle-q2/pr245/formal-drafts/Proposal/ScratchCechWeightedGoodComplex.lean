import Proposal.ScratchCechWeightedBasis
import Proposal.ScratchCechGoodFamilies
import Proposal.ScratchCechNativeDeRham

/-! The ordinary exterior derivatives on all exact affine subopens define a
global complex of presheaves on the weighted threefold. The map from ordinary
forms intertwines the derivative in every exact coordinate frame. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2LogarithmicDifferential CycleQ2LogarithmicChartDerivative
open CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient

namespace CycleQ2.Cech.WeightedGoodComplex

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)

abbrev A (n : ℕ) := Native.P (toBase φ) n

abbrev coords {W : (threefold φ).Opens} (hW : WeightedBasis.Good φ W) :=
  (WeightedBasis.frame φ hW).choose

abbrev basis {W : (threefold φ).Opens} (hW : WeightedBasis.Good φ W) :=
  (WeightedBasis.frame φ hW).choose_spec.choose

theorem basis_exact {W : (threefold φ).Opens} (hW : WeightedBasis.Good φ W) (j : Fin 3) :
    basis φ hW j = KaehlerDifferential.D k (Native.R (toBase φ) W) (coords φ hW j) :=
  (WeightedBasis.frame φ hW).choose_spec.choose_spec j

def localD (n : ℕ) : GoodFamilies.LocalMap (WeightedBasis.Good φ) (A φ n) (A φ (n+1)) where
  app W hW := exteriorD (basis φ hW) n
  natural V W hV hW h s :=
    (pull_d ((Sections.presheaf (toBase φ)).map (homOfLE h).op).hom
      (basis φ hW) (coords φ hW) (basis_exact φ hW)
      (basis φ hV) (coords φ hV) (basis_exact φ hV) n s).symm

theorem square (n : ℕ) (W : (threefold φ).Opens) (hW : WeightedBasis.Good φ W)
    (s : (A φ n).obj (op W)) : (localD φ (n+1)).app W hW ((localD φ n).app W hW s) = 0 :=
  exteriorD_squared (basis φ hW) (coords φ hW) (basis_exact φ hW) n s

/-- The ordinary de Rham differential on arbitrary opens, represented as a
compatible family of differentials of restrictions on the affine basis. -/
def complex : CochainComplex ((threefold φ).Opensᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  GoodFamilies.complex (WeightedBasis.Good φ) (A φ) (localD φ) (square φ)

def fromForms (n : ℕ) : A φ n ⟶ (complex φ).X n :=
  GoodFamilies.unit _ _

/-- Naturality in the identity algebra map identifies all the choices of
exact coordinate frame on W. -/
theorem fromForms_d {W : (threefold φ).Opens} (hW : WeightedBasis.Good φ W)
    {I : Type} [Fintype I] [LinearOrder I]
    (b : Module.Basis I (Native.R (toBase φ) W) (KaehlerDifferential k (Native.R (toBase φ) W)))
    (x : I → Native.R (toBase φ) W)
    (hx : ∀ j, b j = KaehlerDifferential.D k (Native.R (toBase φ) W) (x j))
    (n : ℕ) (s : (A φ n).obj (op W)) :
    ((complex φ).d n (n+1)).app (op W) ((fromForms φ n).app (op W) s) =
      (fromForms φ (n+1)).app (op W) (exteriorD b n s) := by
  have e := pull_d (AlgHom.id k (Native.R (toBase φ) W)) b x hx
    (basis φ hW) (coords φ hW) (basis_exact φ hW) n s
  simp only [Chart.pull_id] at e
  change ((GoodFamilies.complex _ _ _ _).d n (n+1)).app (op W) _ = _
  rw [GoodFamilies.complex_d]
  exact (GoodFamilies.extend_unit _ (localD φ n) W hW s).trans
    (congrArg ((fromForms φ (n+1)).app (op W)) e)

theorem fromForms_isIso (n : ℕ) (W : (threefold φ).Opens) (hW : WeightedBasis.Good φ W) :
    IsIso ((fromForms φ n).app (op W)) :=
  GoodFamilies.unit_isIso _ _ W hW

end CycleQ2.Cech.WeightedGoodComplex
end

#print axioms CycleQ2.Cech.WeightedGoodComplex.complex
#print axioms CycleQ2.Cech.WeightedGoodComplex.fromForms_d
