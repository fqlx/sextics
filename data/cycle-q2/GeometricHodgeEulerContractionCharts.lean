import Proposal.GeometricHodgeEulerChartDerivations
import Proposal.GeometricHodgeEulerContraction
import Proposal.GeometricLiteralThreefoldResidueMinors

/-!
# Residue contraction on the principal gradient charts

Inverting one partial derivative of a four-variable hypersurface gives a
submersive presentation. Its three free Kähler coordinates are the other
three coordinate differentials, in their original order. Dividing their
signed wedge by the chosen partial gives the Poincaré residue. Contraction
with this actual form identifies vector fields with two-forms. The
normalization agrees whenever two partial derivatives are units.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerContractionCharts

open MvPolynomial Module CycleQ2HodgeEulerChartDerivations CycleQ2HodgeEulerContraction
open CycleQ2LiteralThreefoldResidueContraction CycleQ2LiteralThreefoldResidueMinors
open scoped KaehlerDifferential

variable {K : Type} [CommRing K]

abbrev gradientEntry (q : Poly K) (j : Fin 4) := mk q (pderiv j q)
abbrev Patch (q : Poly K) (j : Fin 4) := Localization.Away (gradientEntry q j)

private def presentation (q : Poly K) (j : Fin 4) :
    Algebra.PreSubmersivePresentation K (Hyp q) (Fin 4) Unit where
  toPresentation :=
    { toGenerators := Algebra.Generators.naive (I := Ideal.span ({q} : Set (Poly K)))
      relation := fun _ => q
      span_range_relation_eq_ker := by rw [Algebra.Generators.ker_naive, Set.range_const] }
  map := fun _ => j
  map_inj := fun _ _ _ => Subsingleton.elim _ _

private theorem jacobian_eq (q : Poly K) (j : Fin 4) :
    (presentation q j).jacobian = gradientEntry q j := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

private def smoothPresentation (q : Poly K) (j : Fin 4) :
    Algebra.SubmersivePresentation K (Patch q j) (Unit ⊕ Fin 4) (Unit ⊕ Unit) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway (Patch q j) (gradientEntry q j)).comp (presentation q j)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, jacobian_eq,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) _).mul
      (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) _)

theorem patch_standardSmooth (q : Poly K) (j : Fin 4) :
    Algebra.IsStandardSmoothOfRelativeDimension 3 K (Patch q j) := by
  apply (smoothPresentation q j).isStandardSmoothOfRelativeDimension
  change Nat.card (Unit ⊕ Fin 4) - Nat.card (Unit ⊕ Unit) = 3
  norm_num [Nat.card_eq_fintype_card]

private def omitted (j : Fin 4) (a : Fin 3) : Unit ⊕ Fin 4 := Sum.inr (j.succAbove a)

private theorem omitted_injective (j : Fin 4) : Function.Injective (omitted j) :=
  Sum.inr_injective.comp j.succAbove_right_injective

private theorem complement (q : Poly K) (j : Fin 4) :
    IsCompl (Set.range (omitted j)) (Set.range (smoothPresentation q j).map) := by
  classical
  have hs : Set.range (smoothPresentation q j).map = {Sum.inl (), Sum.inr j} := by
    ext x
    change (∃ u : Unit ⊕ Unit, Sum.elim (fun _ => Sum.inl ()) (fun _ => Sum.inr j) u = x) ↔ _
    simp [Sum.exists, eq_comm]
  rw [hs]
  apply IsCompl.of_eq
  all_goals
    ext x
    cases x with
    | inl u => simp [omitted]
    | inr n =>
        have h : (∃ k, j.succAbove k = n) ↔ n ≠ j := by
          change n ∈ Set.range j.succAbove ↔ _
          rw [Fin.range_succAbove]
          rfl
        simp [omitted, Set.mem_range, h] <;> exact em _

def basis (q : Poly K) (j : Fin 4) :
    Basis (Fin 3) (Patch q j) Ω[Patch q j⁄K] :=
  (smoothPresentation q j).basisKaehlerOfIsCompl (omitted_injective j) (complement q j)

def dx {S : Type} [CommRing S] [Algebra K S] (q : Poly K) (f : Hyp q →ₐ[K] S) (a : Fin 4) :
    Ω[S⁄K] :=
  KaehlerDifferential.D K S (f (mk q (X a)))

abbrev patchMap (q : Poly K) (j : Fin 4) : Hyp q →ₐ[K] Patch q j :=
  IsScalarTower.toAlgHom K (Hyp q) (Patch q j)

theorem basis_apply (q : Poly K) (j : Fin 4) (a : Fin 3) :
    basis q j a = dx q (patchMap q j) (j.succAbove a) := by
  rw [basis, Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  rfl

section Residue
variable {S : Type} [CommRing S] [Algebra K S] (q : Poly K) (f : Hyp q →ₐ[K] S)

theorem gradient_relation : ∑ a : Fin 4, f (gradientEntry q a) • dx q f a = 0 := by
  have h := CycleQ2PolynomialChainRule.apply (f.comp (mk q)) (KaehlerDifferential.D K S) q
  change KaehlerDifferential.D K S (f (mk q q)) = _ at h
  rw [mk_equation, map_zero, map_zero] at h
  exact h.symm

def residueAlong (j : Fin 4) (h : IsUnit (f (gradientEntry q j))) : ⋀[S]^3 Ω[S⁄K] :=
  (↑h.unit⁻¹ : S) • signedOmitted S (dx q f) j

theorem partial_smul_residueAlong (j : Fin 4) (h : IsUnit (f (gradientEntry q j))) :
    f (gradientEntry q j) • residueAlong q f j h = signedOmitted S (dx q f) j := by
  have hu : f (gradientEntry q j) * (↑h.unit⁻¹ : S) = 1 := by
    simpa only [h.unit_spec] using h.unit.mul_inv
  rw [residueAlong, smul_smul, hu, one_smul]

/-- The signed residue agrees on the overlaps of any two gradient opens. -/
theorem residueAlong_eq (j k : Fin 4) (hj : IsUnit (f (gradientEntry q j))) (hk : IsUnit (f (gradientEntry q k))) :
    residueAlong q f j hj = residueAlong q f k hk := by
  apply (IsUnit.smul_left_cancel hj).mp
  apply (IsUnit.smul_left_cancel hk).mp
  rw [partial_smul_residueAlong, smul_comm (f (gradientEntry q k)) (f (gradientEntry q j)), partial_smul_residueAlong]
  exact signedOmitted_cross _ _ (gradient_relation q f) j k

end Residue

def patchUnit (q : Poly K) (j : Fin 4) : (Patch q j)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) (gradientEntry q j)).unit

def patchResidue (q : Poly K) (j : Fin 4) : ⋀[Patch q j]^3 Ω[Patch q j⁄K] :=
  residueAlong q (patchMap q j) j (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) (gradientEntry q j))

theorem patchResidue_eq (q : Poly K) (j : Fin 4) :
    patchResidue q j =
      ((↑((patchUnit q j)⁻¹ * (-1 : (Patch q j)ˣ)^j.val) : Patch q j)) •
        exteriorPower.ιMulti (Patch q j) 3 (basis q j) := by
  have hb : dx q (patchMap q j) ∘ j.succAbove = basis q j :=
    funext (fun a => (basis_apply q j a).symm)
  simp only [patchResidue, residueAlong, signedOmitted, hb, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, patchUnit, mul_smul]

def tangentToTwoForms (q : Poly K) (j : Fin 4) :
    Derivation K (Patch q j) (Patch q j) ≃ₗ[Patch q j] (⋀[Patch q j]^2 Ω[Patch q j⁄K]) :=
  (KaehlerDifferential.linearMapEquivDerivation K (Patch q j)).symm.trans
    (unitContractionEquiv (basis q j) ((patchUnit q j)⁻¹ * (-1 : (Patch q j)ˣ)^j.val))

theorem tangentToTwoForms_apply (q : Poly K) (j : Fin 4) (v : Derivation K (Patch q j) (Patch q j)) :
    tangentToTwoForms q j v = interior 2 v.liftKaehlerDifferential (patchResidue q j) := by
  rw [patchResidue_eq]
  exact unitContractionEquiv_apply _ _ _

/-- In the chart with the degree-one homogeneous coordinate number i set to one,
the oriented Euler volume has the additional sign from omitting that coordinate. -/
def projectiveResidue (q : Poly K) (i j : Fin 4) : ⋀[Patch q j]^3 Ω[Patch q j⁄K] :=
  (-1 : Patch q j)^i.val • patchResidue q j

set_option maxHeartbeats 800000 in
theorem partial_smul_projectiveResidue (q : Poly K) (i j : Fin 4) :
    patchMap q j (gradientEntry q j) • projectiveResidue q i j =
      (-1 : Patch q j)^(i.val + j.val) • exteriorPower.ιMulti (Patch q j) 3 (basis q j) := by
  have hb : dx q (patchMap q j) ∘ j.succAbove = basis q j :=
    funext (fun a => (basis_apply q j a).symm)
  have hc := partial_smul_residueAlong q (patchMap q j) j
    (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) (gradientEntry q j))
  change patchMap q j (gradientEntry q j) • patchResidue q j =
    (-1 : Patch q j)^j.val • exteriorPower.ιMulti (Patch q j) 3 (dx q (patchMap q j) ∘ j.succAbove) at hc
  rw [hb] at hc
  calc
    _ = (-1 : Patch q j)^i.val • (patchMap q j (gradientEntry q j) • patchResidue q j) :=
      smul_comm _ _ _
    _ = (-1 : Patch q j)^i.val • ((-1 : Patch q j)^j.val • exteriorPower.ιMulti _ 3 (basis q j)) :=
      congrArg (fun w : ⋀[Patch q j]^3 Ω[Patch q j⁄K] => (-1 : Patch q j)^i.val • w) hc
    _ = _ := by rw [pow_add, mul_smul]

def projectiveTangentToTwoForms (q : Poly K) (i j : Fin 4) :
    Derivation K (Patch q j) (Patch q j) ≃ₗ[Patch q j] (⋀[Patch q j]^2 Ω[Patch q j⁄K]) :=
  (tangentToTwoForms q j).trans (LinearEquiv.smulOfUnit ((-1 : (Patch q j)ˣ)^i.val))

theorem projectiveTangentToTwoForms_apply (q : Poly K) (i j : Fin 4)
    (v : Derivation K (Patch q j) (Patch q j)) :
    projectiveTangentToTwoForms q i j v =
      interior 2 v.liftKaehlerDifferential (projectiveResidue q i j) := by
  change ((↑((-1 : (Patch q j)ˣ)^i.val) : Patch q j)) • tangentToTwoForms q j v = _
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, tangentToTwoForms_apply,
    projectiveResidue, map_smul]

end CycleQ2HodgeEulerContractionCharts
end

#print axioms CycleQ2HodgeEulerContractionCharts.tangentToTwoForms_apply
#print axioms CycleQ2HodgeEulerContractionCharts.residueAlong_eq
