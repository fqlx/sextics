import Proposal.GeometricHodgeNormalCohomology
import Proposal.GeometricAutomorphismCohomology

/-!
# Normal connecting cocycles from local projective velocities

For any finite open cover of a moving sextic, the differences of local
lifts of a global normal section define a kernel-valued cocycle whose
class is the original Yoneda connecting homomorphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeNormalConnectingCech

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace CategoryTheory.Abelian
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeThreefoldTwist CycleQ2HodgeNormalCohomology CycleQ2HodgeEulerSheaf
open CycleQ2SeedSectionSheafLimits (sectionKernelEquiv sectionKernelEquiv_val sectionKernelEquiv_symm_val)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_comp moduleRes_app)
open CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteInjectiveCech
open CycleQ2InjectiveCech (AbSheaf)
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable {R ι : Type} [CommRing R] (φ : CoeffRing →+* R) (D : ι → (threefold φ).Opens)
variable (q : Γ(twist φ 6,⊤)) (b : ∀ i, Γ(raw φ,D i))
variable (hb : ∀ i, (normalMap φ).app (D i) (b i) = moduleRes (twist φ 6) le_top q)

abbrev F := Add φ (rawTangent φ)

def difference (i j : ι) (W : (threefold φ).Opens) (hi : W ≤ D i) (hj : W ≤ D j) : Γ(rawTangent φ,W) :=
  (sectionKernelEquiv (normalMap φ) W).symm
    ⟨moduleRes (raw φ) hj (b j) - moduleRes (raw φ) hi (b i), by
      change (normalMap φ).app W (_ - _) = 0
      rw [map_sub, ← moduleRes_app, ← moduleRes_app, hb, hb, moduleRes_comp, moduleRes_comp, sub_self]⟩

theorem difference_val (i j : ι) (W : (threefold φ).Opens) (hi : W ≤ D i) (hj : W ≤ D j) :
    (kernel.ι (normalMap φ)).app W (difference φ D q b hb i j W hi hj) =
      moduleRes (raw φ) hj (b j) - moduleRes (raw φ) hi (b i) :=
  sectionKernelEquiv_symm_val (normalMap φ) W _

theorem inclusion_injective (W : (threefold φ).Opens) : Function.Injective ((kernel.ι (normalMap φ)).app W) := by
  intro s t h
  apply (sectionKernelEquiv (normalMap φ) W).injective
  apply Subtype.ext
  rw [sectionKernelEquiv_val, sectionKernelEquiv_val]
  exact h

theorem difference_restrict (i j : ι) {V W : (threefold φ).Opens} (hi : V ≤ D i) (hj : V ≤ D j) (h : W ≤ V) :
    moduleRes (rawTangent φ) h (difference φ D q b hb i j V hi hj) =
      difference φ D q b hb i j W (h.trans hi) (h.trans hj) := by
  apply inclusion_injective
  rw [← moduleRes_app, difference_val, map_sub, moduleRes_comp, moduleRes_comp, difference_val]

def cocycle : One (F φ) D := fun i j => difference φ D q b hb i j _ inf_le_left inf_le_right

theorem edge (i j : ι) (W : (threefold φ).Opens) (hi : W ≤ D i) (hj : W ≤ D j) :
    edgeValue (F φ) D (cocycle φ D q b hb) i j W hi hj = difference φ D q b hb i j W hi hj :=
  difference_restrict φ D q b hb i j inf_le_left inf_le_right (le_inf hi hj)

theorem closed : IsOneCocycle (F φ) D (cocycle φ D q b hb) := by
  intro i j k W hi hj hk
  change edgeValue _ _ _ i k W hi hk = edgeValue _ _ _ i j W hi hj + edgeValue _ _ _ j k W hj hk
  rw [edge, edge, edge]
  apply inclusion_injective
  rw [map_add, difference_val, difference_val, difference_val]
  abel

theorem cechClass [Fintype ι] (hg : IsUnit (φ goodParameter)) (hD : (⨆ i, D i) = ⊤) :
    cechOneClass D hD (cocycle φ D q b hb) (closed φ D q b hb) = connecting φ hg q := by
  have h := CycleQ2AutomorphismCohomology.cechOneClass_of_lifts D hD (addNormal_exact φ hg)
    (cocycle φ D q b hb) (closed φ D q b hb) b q
    (by intro i j W hi hj; rw [edge]; exact (difference_val φ D q b hb i j W hi hj).symm)
    (by funext i; exact (hb i).symm)
  refine h.trans ?_
  rw [CycleQ2ThreeOpenInjectiveComparison.sectionExtZero_eq_hzero]
  rfl

end CycleQ2HodgeNormalConnectingCech
end
#print axioms CycleQ2HodgeNormalConnectingCech.cechClass
