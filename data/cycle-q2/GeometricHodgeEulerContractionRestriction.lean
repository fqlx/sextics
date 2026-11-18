import Proposal.GeometricHodgeEuler
import Proposal.SolutionSupport07Part01
import Proposal.GeometricHodgeEulerContractionCharts

/-!
# Restriction of the normalized sextic residue and its contraction

The Kähler pullback carries each signed residue to the same normalized form
on the target algebra. Hence distinct gradient charts agree on every common
localization, and contraction commutes with that restriction for compatible
derivations. Specializing the original weighted sextic family identifies the
vector fields on each such chart with genuine two-forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerContractionRestriction

open MvPolynomial CycleQ2HodgeEulerChartDerivations CycleQ2HodgeEulerContractionCharts
open CycleQ2LiteralThreefoldResidueContraction CycleQ2GeometricExteriorSheaf
open CycleQ2LiteralThreefoldResidueMinors (signedOmitted)
open scoped KaehlerDifferential

variable {K S T : Type} [CommRing K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]

def pullOne (g : S →ₐ[K] T) : Ω[S⁄K] →ₛₗ[g.toRingHom] Ω[T⁄K] := by
  letI := g.toRingHom.toAlgebra
  letI : IsScalarTower K S T := IsScalarTower.of_algHom g
  exact { toFun := KaehlerDifferential.map K K S T
          map_add' := (KaehlerDifferential.map K K S T).map_add
          map_smul' := fun a ω => by
            rw [map_smul]
            exact (IsScalarTower.algebraMap_smul (R := S) (A := T) a
              (KaehlerDifferential.map K K S T ω)).symm }

theorem pullOne_D (g : S →ₐ[K] T) (x : S) :
    pullOne g (KaehlerDifferential.D K S x) = KaehlerDifferential.D K T (g x) := by
  let _ := g.toRingHom.toAlgebra
  let _ : IsScalarTower K S T := IsScalarTower.of_algHom g
  exact KaehlerDifferential.map_D K K S T x

def pull (g : S →ₐ[K] T) (n : ℕ) :
    (⋀[S]^n Ω[S⁄K]) →ₛₗ[g.toRingHom] (⋀[T]^n Ω[T⁄K]) :=
  exteriorMap g.toRingHom (pullOne g) n

theorem pull_wedge (g : S →ₐ[K] T) (n : ℕ) (w : Fin n → Ω[S⁄K]) :
    pull g n (exteriorPower.ιMulti S n w) =
      exteriorPower.ιMulti T n (fun a => pullOne g (w a)) :=
  exteriorMap_wedge ..

theorem pull_residue (q : Poly K) (f : Hyp q →ₐ[K] S) (g : S →ₐ[K] T)
    (j : Fin 4) (hj : IsUnit (f (gradientEntry q j))) :
    pull g 3 (residueAlong q f j hj) = residueAlong q (g.comp f) j (hj.map g.toMonoidHom) := by
  apply (IsUnit.smul_left_cancel (hj.map g.toMonoidHom)).mp
  calc
    _ = pull g 3 (f (gradientEntry q j) • residueAlong q f j hj) := ((pull g 3).map_smulₛₗ _ _).symm
    _ = signedOmitted T (dx q (g.comp f)) j := by
      rw [partial_smul_residueAlong, signedOmitted, map_smulₛₗ, pull_wedge]
      simp only [RingHom.map_pow, map_neg, map_one]
      unfold signedOmitted dx
      simp only [Function.comp_apply, pullOne_D, AlgHom.comp_apply]
      rfl
    _ = _ := (partial_smul_residueAlong q (g.comp f) j _).symm

def fromPatch (q : Poly K) (j : Fin 4) (f : Hyp q →ₐ[K] S) (hj : IsUnit (f (gradientEntry q j))) :
    Patch q j →ₐ[K] S :=
  IsLocalization.Away.liftAlgHom (gradientEntry q j) (f := f) hj

theorem fromPatch_comp (q : Poly K) (j : Fin 4) (f : Hyp q →ₐ[K] S) (hj : IsUnit (f (gradientEntry q j))) :
    (fromPatch q j f hj).comp (patchMap q j) = f := by
  apply AlgHom.ext
  intro x
  exact IsLocalization.lift_eq _ x

theorem pull_patchResidue (q : Poly K) (j : Fin 4) (f : Hyp q →ₐ[K] S) (hj : IsUnit (f (gradientEntry q j))) :
    pull (fromPatch q j f hj) 3 (patchResidue q j) = residueAlong q f j hj := by
  rw [patchResidue, pull_residue]
  congr 1
  exact fromPatch_comp q j f hj

theorem common_open (q : Poly K) (j k : Fin 4) (f : Hyp q →ₐ[K] S)
    (hj : IsUnit (f (gradientEntry q j))) (hk : IsUnit (f (gradientEntry q k))) :
    pull (fromPatch q j f hj) 3 (patchResidue q j) =
      pull (fromPatch q k f hk) 3 (patchResidue q k) := by
  rw [pull_patchResidue, pull_patchResidue, residueAlong_eq q f j k hj hk]

private theorem pull_covector (g : S →ₐ[K] T) (v : Derivation K S S) (u : Derivation K T T)
    (hu : ∀ x, u (g x) = g (v x)) (ω : Ω[S⁄K]) :
    u.liftKaehlerDifferential (pullOne g ω) = g (v.liftKaehlerDifferential ω) := by
  have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D K S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [pullOne_D, Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D, hu]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | smul a w _ hw => simp only [map_smulₛₗ, smul_eq_mul, hw, map_mul]; rfl

theorem pull_contraction (g : S →ₐ[K] T) (v : Derivation K S S) (u : Derivation K T T)
    (hu : ∀ x, u (g x) = g (v x)) (ω : ⋀[S]^3 Ω[S⁄K]) :
    pull g 2 (interior 2 v.liftKaehlerDifferential ω) =
      interior 2 u.liftKaehlerDifferential (pull g 3 ω) :=
  (interior_natural g.toRingHom (pullOne g) _ _ (pull_covector g v u hu) 2 ω).symm

/-- On any localization of the chart the canonical extension of a vector
field satisfies contraction naturality without a compatibility hypothesis. -/
theorem pull_contraction_localization [Algebra S T] [IsScalarTower K S T]
    (M : Submonoid S) [IsLocalization M T] (v : Derivation K S S) (ω : ⋀[S]^3 Ω[S⁄K]) :
    pull (IsScalarTower.toAlgHom K S T) 2 (interior 2 v.liftKaehlerDifferential ω) =
      interior 2 (CycleQ2LocalizationDerivation.extend (S := T) M v).liftKaehlerDifferential
        (pull (IsScalarTower.toAlgHom K S T) 3 ω) :=
  pull_contraction _ _ _ (CycleQ2LocalizationDerivation.extend_map M v) ω

/-- Restricting the weighted Euler numerator to the affine slice picks out the
summand of its normalized coordinate. This fixes the sign before quotienting
by the hypersurface equation. -/
theorem dehomogeneousEulerNumerator (i : Fin 4) :
    (∑ j : Fin 5, (-1 : Poly K)^j.val •
      (((CycleQ2IncidenceNormalForm.fullGrading j).1 : Poly K) *
        CycleQ2HodgeEuler.dehom (R := K) i (X j)) •
      exteriorPower.ιMulti (Poly K) 4
        (fun k : Fin 4 => KaehlerDifferential.D K (Poly K)
          (CycleQ2HodgeEuler.dehom i (X (j.succAbove k))))) =
    (-1 : Poly K)^i.val • exteriorPower.ιMulti (Poly K) 4
      (fun k : Fin 4 => KaehlerDifferential.D K (Poly K) (X k)) := by
  classical
  rw [Finset.sum_eq_single i.castSucc]
  · have hw : (CycleQ2IncidenceNormalForm.fullGrading i.castSucc).1 = 1 := by fin_cases i <;> rfl
    simp only [hw, Nat.cast_one, CycleQ2HodgeEuler.dehom_X_self, mul_one, one_smul,
      CycleQ2HodgeEuler.dehom_X_succAbove]
    rfl
  · intro j _ hj
    have hmem : i.castSucc ∈ Set.range j.succAbove := by
      rw [Fin.range_succAbove]; exact Ne.symm hj
    obtain ⟨k, hk⟩ := hmem
    have hz : exteriorPower.ιMulti (Poly K) 4 (fun a : Fin 4 =>
        KaehlerDifferential.D K (Poly K) (CycleQ2HodgeEuler.dehom i (X (j.succAbove a)))) = 0 := by
      apply (exteriorPower.ιMulti (Poly K) 4).map_coord_zero k
      rw [hk, CycleQ2HodgeEuler.dehom_X_self, Derivation.map_one_eq_zero]
    rw [hz, smul_zero, smul_zero]
  · simp

open CycleQ2GenericSexticGradient

/-- Contraction on the indicated gradient open of the original normalized weighted family. -/
abbrev familyContraction (φ : CoeffRing →+* K) (i j : Fin 4) :=
  projectiveTangentToTwoForms (CycleQ2HodgeEuler.F φ i) i j

theorem familyContraction_apply (φ : CoeffRing →+* K) (i j : Fin 4)
    (v : Derivation K (Patch (CycleQ2HodgeEuler.F φ i) j) (Patch (CycleQ2HodgeEuler.F φ i) j)) :
    familyContraction φ i j v =
      interior 2 v.liftKaehlerDifferential (projectiveResidue (CycleQ2HodgeEuler.F φ i) i j) :=
  projectiveTangentToTwoForms_apply _ _ _ v

/-- Two gradient pivots give the same restricted family contraction for
vector fields inducing the same derivation on their common open. -/
theorem familyContraction_common (φ : CoeffRing →+* K) (i j k : Fin 4)
    (f : Hyp (CycleQ2HodgeEuler.F φ i) →ₐ[K] S)
    (hj : IsUnit (f (gradientEntry (CycleQ2HodgeEuler.F φ i) j)))
    (hk : IsUnit (f (gradientEntry (CycleQ2HodgeEuler.F φ i) k)))
    (v : Derivation K (Patch (CycleQ2HodgeEuler.F φ i) j) (Patch (CycleQ2HodgeEuler.F φ i) j))
    (w : Derivation K (Patch (CycleQ2HodgeEuler.F φ i) k) (Patch (CycleQ2HodgeEuler.F φ i) k))
    (u : Derivation K S S)
    (hv : ∀ x, u (fromPatch _ j f hj x) = fromPatch _ j f hj (v x))
    (hw : ∀ x, u (fromPatch _ k f hk x) = fromPatch _ k f hk (w x)) :
    pull (fromPatch _ j f hj) 2 (familyContraction φ i j v) =
      pull (fromPatch _ k f hk) 2 (familyContraction φ i k w) := by
  rw [familyContraction_apply, familyContraction_apply,
    pull_contraction _ v u hv, pull_contraction _ w u hw]
  apply congrArg
  simp only [projectiveResidue, map_smulₛₗ, map_pow, map_neg, map_one]
  rw [common_open _ j k f hj hk]

end CycleQ2HodgeEulerContractionRestriction
end

#print axioms CycleQ2HodgeEulerContractionRestriction.common_open
#print axioms CycleQ2HodgeEulerContractionRestriction.pull_contraction
#print axioms CycleQ2HodgeEulerContractionRestriction.dehomogeneousEulerNumerator
#print axioms CycleQ2HodgeEulerContractionRestriction.familyContraction_apply
