import Proposal.GeometricHodgeEulerContractionTransition
import Proposal.GeometricHodgeEulerContractionRestriction
import Proposal.GeometricLiteralThreefoldResidueGluing

/-!
# The moving sextic residue on changes of projective chart

The ambient ring is the principal localization of the normalized polynomial
ring. In every algebra of this overlap on which the sextic vanishes, the two
oriented residues agree whenever the chosen partial on each side is a unit.
The two partials can be chosen independently.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeEulerContractionGluing

open Module MvPolynomial CycleQ2HodgeEuler CycleQ2GenericSexticGradient
open CycleQ2HodgeEulerContractionTransition CycleQ2HodgeEulerChartDerivations
open CycleQ2HodgeEulerContractionCharts CycleQ2LiteralThreefoldResidueMinors
open CycleQ2HodgeEulerContractionRestriction
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2LiteralThreefoldResidueGluing CycleQ2ExteriorTopBaseChange
open scoped KaehlerDifferential TensorProduct

variable {K : Type} [CommRing K]
abbrev Ambient (K : Type) [CommRing K] (a : Fin 3) :=
  Localization.Away (X a.castSucc : Poly K)

def point (i : Fin 4) (a : Fin 3) : Fin 5 → Ambient K a :=
  i.castSucc.insertNth 1 (fun b => algebraMap (Poly K) (Ambient K a) (X b))

def inverse (K : Type) [CommRing K] (a : Fin 3) : Ambient K a :=
  IsLocalization.Away.invSelf (X a.castSucc : Poly K)

@[simp] theorem point_self (i : Fin 4) (a : Fin 3) : point (K := K) i a i.castSucc = 1 := by
  simp [point]

@[simp] theorem point_free (i : Fin 4) (a : Fin 3) (b : Fin 4) :
    point (K := K) i a (i.castSucc.succAbove b) = algebraMap (Poly K) (Ambient K a) (X b) := by
  simp [point]

theorem inverse_mul (i : Fin 4) (a : Fin 3) : inverse K a * point i a (i.succAbove a).castSucc = 1 := by
  have h : (i.succAbove a).castSucc = i.castSucc.succAbove a.castSucc := by
    fin_cases i <;> fin_cases a <;> rfl
  rw [h, point_free, mul_comm]
  exact IsLocalization.Away.mul_invSelf _

def ambientBasis (a : Fin 3) : Basis (Fin 4) (Ambient K a) Ω[Ambient K a⁄K] := by
  letI : Algebra.FormallyEtale (Poly K) (Ambient K a) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Ambient K a) (Submonoid.powers (X a.castSucc : Poly K))
  exact ((KaehlerDifferential.mvPolynomialBasis K (Fin 4)).baseChange (Ambient K a)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Poly K) (Ambient K a))

theorem ambientBasis_apply (a : Fin 3) (b : Fin 4) :
    ambientBasis (K := K) a b = KaehlerDifferential.D K (Ambient K a) (algebraMap (Poly K) _ (X b)) := by
  simp only [ambientBasis, Basis.map_apply, Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  change KaehlerDifferential.mapBaseChange K (Poly K) (Ambient K a) _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

section Algebra
variable {B S : Type} [CommRing B] [CommRing S] [Algebra K B] [Algebra K S] [Algebra B S] [IsScalarTower K B S]

def evaluate (q : Poly K) (x : Fin 4 → B) (hq : algebraMap B S (aeval x q) = 0) : Hyp q →ₐ[K] S :=
  let f := (IsScalarTower.toAlgHom K B S).comp (aeval x)
  Ideal.Quotient.liftₐ _ f (fun _ hp =>
    (Ideal.span_singleton_le_iff_mem (RingHom.ker f.toRingHom)).mpr hq hp)

@[simp] theorem evaluate_poly (q : Poly K) (x : Fin 4 → B) (hq : algebraMap B S (aeval x q) = 0)
    (p : Poly K) : evaluate q x hq (mk q p) = algebraMap B S (aeval x p) := rfl

def restricted (x : Fin 4 → B) (j : Fin 4) : S ⊗[B] Ω[B⁄K] := (1 : S) ⊗ₜ[B] KaehlerDifferential.D K B (x j)

omit [Algebra K S] [IsScalarTower K B S] in
private theorem restricted_fun (x : Fin 4 → B) :
    restricted (K := K) (S := S) x = fun d => (1 : S) ⊗ₜ[B] KaehlerDifferential.D K B (x d) := rfl

theorem restricted_dx (q : Poly K) (x : Fin 4 → B) (hq : algebraMap B S (aeval x q) = 0) :
    KaehlerDifferential.mapBaseChange K B S ∘ restricted (K := K) (S := S) x = dx q (evaluate q x hq) := by
  funext b
  simp only [Function.comp_apply, restricted, dx, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D, evaluate_poly, aeval_X]

theorem restricted_gradient (q : Poly K) (x : Fin 4 → B) (hq : algebraMap B S (aeval x q) = 0) :
    (1 : S) ⊗ₜ[B] KaehlerDifferential.D K B (aeval x q) =
      ∑ b, evaluate q x hq (gradientEntry q b) • restricted (K := K) (S := S) x b := by
  rw [CycleQ2PolynomialChainRule.apply (aeval x) (KaehlerDifferential.D K B) q, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [TensorProduct.tmul_smul, aeval_X, restricted, gradientEntry, evaluate_poly]
  exact (IsScalarTower.algebraMap_smul S _ _).symm

theorem each_gradient (q : Poly K) (f : Hyp q →ₐ[K] S) (j : Fin 4) (hj : IsUnit (f (gradientEntry q j))) (b : Fin 4) :
    f (gradientEntry q b) • residueAlong q f j hj = signedOmitted S (dx q f) b := by
  apply (IsUnit.smul_left_cancel hj).mp
  rw [smul_comm (f (gradientEntry q j)) (f (gradientEntry q b)), partial_smul_residueAlong]
  exact signedOmitted_cross _ _ (gradient_relation q f) j b

private theorem pull_projectiveContraction (q : Poly K) (i j : Fin 4) (f : Hyp q →ₐ[K] S)
    (hj : IsUnit (f (gradientEntry q j))) (v : Derivation K (Patch q j) (Patch q j)) (u : Derivation K S S)
    (hv : ∀ x, u (fromPatch q j f hj x) = fromPatch q j f hj (v x)) :
    pull (fromPatch q j f hj) 2 (projectiveTangentToTwoForms q i j v) =
      interior 2 u.liftKaehlerDifferential ((-1 : S)^i.val • residueAlong q f j hj) := by
  rw [projectiveTangentToTwoForms_apply, pull_contraction _ v u hv]
  simp only [projectiveResidue, map_smulₛₗ, map_pow, map_neg, map_one, pull_patchResidue]

private theorem bezout (a : Fin 4 → S) (j : Fin 4) (h : IsUnit (a j)) :
    ∑ b, (if b = j then (↑h.unit⁻¹ : S) else 0) * a b = 1 := by
  rw [Finset.sum_eq_single j]
  · rw [if_pos (rfl : j = j)]
    simpa only [h.unit_spec] using h.unit.inv_mul
  · intro b _ hb; simp [hb]
  · simp

end Algebra

section Overlap
variable (φ : CoeffRing →+* K) (i : Fin 4) (a : Fin 3)
variable (S : Type) [CommRing S] [Algebra K S] [Algebra (Ambient K a) S] [IsScalarTower K (Ambient K a) S]

abbrev old := point (K := K) i a ∘ i.castSucc.succAbove
abbrev newCoord := scaledPoint (point (K := K) i a) (inverse K a) ∘ (i.succAbove a).castSucc.succAbove

omit [Algebra K S] [IsScalarTower K (Ambient K a) S] in
theorem new_equation (hf : algebraMap (Ambient K a) S (aeval (old (K := K) i a) (F φ i)) = 0) :
    algebraMap (Ambient K a) S (aeval (newCoord (K := K) i a) (F φ (i.succAbove a))) = 0 := by
  rw [newCoord, equation_change φ i _ _ (point_self i a) _ (inverse_mul i a), map_mul, ← old, hf, mul_zero]

set_option maxHeartbeats 800000 in
theorem residue_change (hf : algebraMap (Ambient K a) S (aeval (old (K := K) i a) (F φ i)) = 0)
    (j l : Fin 4)
    (hj : IsUnit (evaluate _ _ hf (gradientEntry (F φ i) j)))
    (hl : IsUnit (evaluate _ _ (new_equation φ i a S hf) (gradientEntry (F φ (i.succAbove a)) l))) :
    (-1 : S)^(i.succAbove a).val •
        residueAlong _ (evaluate _ _ (new_equation φ i a S hf)) l hl =
      (-1 : S)^i.val • residueAlong _ (evaluate _ _ hf) j hj := by
  let k := i.succAbove a
  let hnew := new_equation φ i a S hf
  let fx := evaluate _ _ hf
  let fy := evaluate _ _ hnew
  let b := (ambientBasis (K := K) a).baseChange S
  let v := restricted (K := K) (S := S) (newCoord (K := K) i a)
  let Q := KaehlerDifferential.mapBaseChange K (Ambient K a) S
  let g := (algebraMap (Ambient K a) S (inverse K a)) ^ 6
  let row := fun d => fx (gradientEntry (F φ i) d)
  let row' := fun d => fy (gradientEntry (F φ k) d)
  have hb : ⇑b = restricted (K := K) (S := S) (old (K := K) i a) := by
    funext d
    simp only [b, Basis.baseChange_apply, ambientBasis_apply, restricted, old, Function.comp_apply, point_free]
  have hx : Q ∘ b = dx (F φ i) fx := by rw [hb]; exact restricted_dx _ _ _
  have hy : Q ∘ v = dx (F φ k) fy := restricted_dx _ _ _
  have hq : ∑ d, row d • Q (b d) = 0 := by
    change ∑ d, row d • (Q ∘ b) d = 0
    rw [hx]
    exact CycleQ2HodgeEulerContractionCharts.gradient_relation (F φ i) fx
  have hn : ∑ d, row' d • v d = g • ∑ d, row d • b d := by
    rw [hb]
    change (∑ d, evaluate _ _ hnew (gradientEntry _ d) • restricted (K := K) (S := S) (newCoord (K := K) i a) d) =
      _ • ∑ d, evaluate _ _ hf (gradientEntry _ d) • restricted (K := K) (S := S) (old (K := K) i a) d
    rw [← restricted_gradient, ← restricted_gradient]
    exact CycleQ2HodgeEulerContractionTransition.conormal_change φ i k _ (point_self i a) _ (inverse_mul i a) hf
  have hg : IsUnit g :=
    ((isUnit_iff_exists_inv.mpr ⟨_, inverse_mul (K := K) i a⟩).map (algebraMap (Ambient K a) S)).pow 6
  have hv : (-1 : S)^k.val * b.det v = g * (-1 : S)^i.val := by
    let _ : Algebra ℂ K := (φ.comp (C : ℂ →+* CoeffRing)).toAlgebra
    have h := congrArg (topBaseChange (S := S) (ambientBasis (K := K) a))
      (orientedVolume_change (K := K) i a _ (point_self i a) _ (inverse_mul i a))
    have hw : (-1 : S)^k.val • exteriorPower.ιMulti S 4 v =
        g • ((-1 : S)^i.val • exteriorPower.ιMulti S 4 b) := by
      rw [hb]
      simpa only [g, k, v, orientedVolume, volume, topBaseChange_wedge, map_smulₛₗ, map_pow,
        map_neg, map_one, old, newCoord, restricted_fun, Function.comp_def] using h
    have hh := congrArg (topCoordinate b) hw
    simp only [map_smul, smul_eq_mul] at hh
    rw [topCoordinate_basis, mul_one, topCoordinate_wedge] at hh
    exact hh
  apply bezout_residue_change b Q row row' _ _ (bezout row j hj) (bezout row' l hl) v g _ _ hg hv hn hq
  · intro d; rw [hx]; exact each_gradient _ _ j hj d
  · intro d; rw [hy]; exact each_gradient _ _ l hl d

/-- The projectively oriented local equivalences induce the same two-form
for vector fields that restrict to the same derivation on the overlap. -/
theorem contraction_change (hf : algebraMap (Ambient K a) S (aeval (old (K := K) i a) (F φ i)) = 0)
    (j l : Fin 4)
    (hj : IsUnit (evaluate _ _ hf (gradientEntry (F φ i) j)))
    (hl : IsUnit (evaluate _ _ (new_equation φ i a S hf) (gradientEntry (F φ (i.succAbove a)) l)))
    (v : Derivation K (Patch (F φ i) j) (Patch (F φ i) j))
    (w : Derivation K (Patch (F φ (i.succAbove a)) l) (Patch (F φ (i.succAbove a)) l))
    (u : Derivation K S S)
    (hv : ∀ z, u (fromPatch _ j (evaluate _ _ hf) hj z) = fromPatch _ j (evaluate _ _ hf) hj (v z))
    (hw : ∀ z, u (fromPatch _ l (evaluate _ _ (new_equation φ i a S hf)) hl z) =
      fromPatch _ l (evaluate _ _ (new_equation φ i a S hf)) hl (w z)) :
    pull (fromPatch _ l (evaluate _ _ (new_equation φ i a S hf)) hl) 2 (familyContraction φ (i.succAbove a) l w) =
      pull (fromPatch _ j (evaluate _ _ hf) hj) 2 (familyContraction φ i j v) := by
  rw [familyContraction, familyContraction, pull_projectiveContraction _ _ _ _ _ w u hw,
    pull_projectiveContraction _ _ _ _ _ v u hv, residue_change φ i a S hf j l hj hl]

end Overlap
end CycleQ2HodgeEulerContractionGluing
end

#print axioms CycleQ2HodgeEulerContractionGluing.residue_change

#print axioms CycleQ2HodgeEulerContractionGluing.contraction_change
