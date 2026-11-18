import Proposal.ScratchCechNativeDeRham
import Proposal.ScratchWeightedIntersectionFrame

/-! # Čech de Rham residue classes on the weighted moving threefold

The terms and maps use the literal structure sheaf rings of the sixteen
gradient opens and their finite intersections. The signed residue data in
degrees (0,3), (1,2), (2,1) represent a degree-three class; all cochains
of total degree two supply the boundary subgroup. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CycleQ2.Cech CycleQ2CechDeRhamTotalThree
open CycleQ2WeightedResidueAtlas CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient

namespace CycleQ2WeightedNativeCech

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)

private theorem haveFrame (p : ℕ) (v : Fin (p+1) → Index) :
    ∃ (x : Fin 3 → Native.ringAt (toBase φ) (U φ) v)
      (b : Module.Basis (Fin 3) (Native.ringAt (toBase φ) (U φ) v)
        (KaehlerDifferential k (Native.ringAt (toBase φ) (U φ) v))),
      ∀ i, b i = KaehlerDifferential.D k _ (x i) := by
  unfold Native.ringAt
  rw [intersection_eq_iInf]
  exact CycleQ2WeightedIntersectionFrame.simplex_frame φ v

/-- The exact coordinate frames on all intersections of the weighted gradient
cover, including its higher simplices. -/
def frames : Native.Frames (toBase φ) (U φ) 3 where
  coords p v := (haveFrame φ p v).choose
  basis p v := (haveFrame φ p v).choose_spec.choose
  exact_coord p v := (haveFrame φ p v).choose_spec.choose_spec

abbrev double := Native.double (toBase φ) (U φ) (frames φ)
abbrev HThree := CycleQ2CechDeRhamTotalThree.HThree (double φ)

/-- The actual degree-three class of the three Čech residues. -/
def residue (a : (double φ).X 0 3) (b : (double φ).X 1 2) (c : (double φ).X 2 1)
    (ha : (double φ).v 0 3 a = 0) (hb : (double φ).h 0 3 a = -((double φ).v 1 2 b))
    (hc : (double φ).h 1 2 b = (double φ).v 2 1 c) (hd : (double φ).h 2 1 c = 0) :
    HThree φ :=
  classOf _ (residueCycle _ a b c ha hb hc hd)

end CycleQ2WeightedNativeCech
end
#print axioms CycleQ2WeightedNativeCech.frames
#print axioms CycleQ2WeightedNativeCech.residue
