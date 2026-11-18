import Proposal.GeometricGenericWeightedDifferentials
import Proposal.GeometricGenericWeightedFieldTransfer
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Exterior differentiation on the weighted three-dimensional function field

The degree-two differential acts on the genuine exterior square of the
relative Kähler module. On a generator `a db ∧ dc` it gives
`da ∧ db ∧ dc`. In the coordinate volume its coefficient is the divergence
of the signed coefficients of the two-form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace CycleQ2GenericWeightedExterior

open scoped BigOperators

private def omittedIndex (i : Fin 3) : Set.powersetCard (Fin 3) 2 :=
  ⟨{i}ᶜ, by simp [Finset.card_compl]⟩

private def omittedEquiv : Fin 3 ≃ Set.powersetCard (Fin 3) 2 := Equiv.ofBijective omittedIndex (by
  constructor
  · intro i j hij
    have h := congrArg (fun s : Set.powersetCard (Fin 3) 2 => (s : Finset (Fin 3))ᶜ) hij
    simpa only [omittedIndex, compl_compl, Finset.singleton_inj] using h
  · intro s
    have hc : ((s : Finset (Fin 3))ᶜ).card = 1 := by simp [Finset.card_compl]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨i, Subtype.ext ?_⟩
    change {i}ᶜ = (s : Finset (Fin 3))
    rw [← hi, compl_compl])

section Coordinates

variable {L W : Type*} [Field L] [Field W] [Algebra L W]

abbrev Form (L W : Type*) [Field L] [Field W] [Algebra L W] (p : ℕ) := ⋀[W]^p Ω[W⁄L]

variable (B : Module.Basis (Fin 3) W Ω[W⁄L]) (D : Fin 3 → Derivation L W W)

/-- The two-form basis indexed by the omitted coordinate in the ordered volume. -/
def twoBasis : Module.Basis (Fin 3) W (Form L W 2) :=
  (B.exteriorPower 2).reindex omittedEquiv.symm

private theorem twoBasis_apply (i : Fin 3) :
    twoBasis B i = exteriorPower.ιMulti W 2 (i.removeNth B) := by
  rw [twoBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change B.exteriorPower 2 (omittedIndex i) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply, omittedIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Fin.removeNth]
  rfl

private theorem twoBasis_repr_wedge (u : Fin 2 → Ω[W⁄L]) (i : Fin 3) :
    (twoBasis B).repr (exteriorPower.ιMulti W 2 u) i =
      (Matrix.of fun j k => B.repr (u j) (i.succAbove k)).det := by
  rw [twoBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm]
  change (B.exteriorPower 2).repr _ (omittedIndex i) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Set.powersetCard.ofFinEmbEquiv_symm_apply, omittedIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Module.Basis.coord_apply]
  rfl

/-- The ordered coordinate volume. -/
def volume : Form L W 3 := exteriorPower.ιMulti W 3 B

private def topIndex : Set.powersetCard (Fin 3) 3 := ⟨Finset.univ, by simp⟩

private theorem topIndex_unique (s : Set.powersetCard (Fin 3) 3) : s = topIndex := by
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp)

private theorem top_order (j : Fin 3) : Set.powersetCard.ofFinEmbEquiv.symm topIndex j = j := by
  have h : (fun i : Fin 3 => i) = (Finset.univ : Finset (Fin 3)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact (congrFun h j).symm

private theorem topBasis_apply : B.exteriorPower 3 topIndex = volume B := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family volume
  congr 1
  funext j
  simp only [Function.comp_apply, top_order]

private def volumeCoefficient : Form L W 3 →ₗ[W] W := (B.exteriorPower 3).coord topIndex

private theorem volumeCoefficient_volume : volumeCoefficient B (volume B) = 1 := by
  rw [← topBasis_apply]
  simp [volumeCoefficient]

private theorem wedge_three (u : Fin 3 → Ω[W⁄L]) :
    exteriorPower.ιMulti W 3 u = (Matrix.of fun j k => B.repr (u j) k).det • volume B := by
  calc
    _ = ∑ s, (B.exteriorPower 3).repr (exteriorPower.ιMulti W 3 u) s • (B.exteriorPower 3) s :=
      ((B.exteriorPower 3).sum_repr _).symm
    _ = _ := by
      rw [Finset.sum_eq_single topIndex]
      · rw [topBasis_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
        simp only [top_order, Module.Basis.coord_apply]
      · intro i _ hi
        exact (hi (topIndex_unique i)).elim
      · simp

/-- Exterior differentiation from degree two to degree three in the exact coordinate basis. -/
def exteriorD2 : Form L W 2 →ₗ[L] Form L W 3 :=
  ∑ i : Fin 3,
    ((LinearMap.toSpanSingleton W _ ((-1 : W) ^ i.val • volume B)).restrictScalars L).comp
      ((D i).toLinearMap.comp (((twoBasis B).coord i).restrictScalars L))

private theorem exteriorD2_apply (η : Form L W 2) :
    exteriorD2 B D η = (∑ i, (-1 : W) ^ i.val * D i ((twoBasis B).repr η i)) • volume B := by
  simp only [exteriorD2, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply,
    Derivation.coeFn_coe, smul_smul, ← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The sign includes the position of the omitted coordinate. -/
def signedCoefficients (η : Form L W 2) (i : Fin 3) : W :=
  (-1 : W) ^ i.val * (twoBasis B).repr η i

theorem exteriorD2_divergence (η : Form L W 2) :
    exteriorD2 B D η = (∑ i, D i (signedCoefficients B η i)) • volume B := by
  rw [exteriorD2_apply]
  simp only [signedCoefficients, Derivation.leibniz, Derivation.leibniz_pow, map_neg,
    Derivation.map_one_eq_zero, neg_zero, smul_eq_mul, mul_zero, smul_zero, add_zero]

theorem exact_volume_iff_divergence (ρ : W) :
    (∃ η : Form L W 2, exteriorD2 B D η = ρ • volume B) ↔ ∃ v : Fin 3 → W, ∑ i, D i (v i) = ρ := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨signedCoefficients B η, ?_⟩
    have h := congrArg (volumeCoefficient B) hη
    simpa only [exteriorD2_divergence, map_smul, volumeCoefficient_volume, smul_eq_mul, mul_one] using h
  · rintro ⟨v, hv⟩
    let η := (twoBasis B).equivFun.symm (fun i => (-1 : W) ^ i.val * v i)
    refine ⟨η, ?_⟩
    have he (i : Fin 3) : signedCoefficients B η i = v i := by
      have hrepr : (twoBasis B).repr η i = (-1 : W) ^ i.val * v i :=
        Module.Basis.coord_equivFun_symm (twoBasis B) i _
      rw [signedCoefficients, hrepr, ← mul_assoc, ← pow_add, show i.val + i.val = 2 * i.val by omega, pow_mul]
      simp
    simp only [exteriorD2_divergence, he, hv]

/-- The derivative of a scalar times the signed minor vector is the
Jacobian determinant. The mixed second-derivative terms cancel in pairs. -/
private theorem divergence_minors {L W : Type*} [Field L] [Field W] [Algebra L W]
    (D : Fin 3 → Derivation L W W) (hD : ∀ i j, Function.Commute (D i) (D j)) (a b c : W) :
    (∑ i : Fin 3, (-1 : W) ^ i.val *
      D i (a * (Matrix.of fun s t : Fin 2 => D (i.succAbove t) (![b, c] s)).det)) =
      (Matrix.of fun s t : Fin 3 => D t (![a, b, c] s)).det := by
  rw [Fin.sum_univ_three, Matrix.det_fin_three]
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  change (-1 : W) ^ 0 *
        D 0 (a * (D 1 b * D 2 c - D 2 b * D 1 c)) +
      (-1 : W) ^ 1 * D 1 (a * (D 0 b * D 2 c - D 2 b * D 0 c)) +
      (-1 : W) ^ 2 * D 2 (a * (D 0 b * D 1 c - D 1 b * D 0 c)) =
      D 0 a * D 1 b * D 2 c - D 0 a * D 2 b * D 1 c -
      D 1 a * D 0 b * D 2 c + D 1 a * D 2 b * D 0 c +
      D 2 a * D 0 b * D 1 c - D 2 a * D 1 b * D 0 c
  simp only [map_sub, Derivation.leibniz, smul_eq_mul]
  rw [hD 1 0 b, hD 1 0 c, hD 2 0 b, hD 2 0 c, hD 2 1 b, hD 2 1 c]
  ring

/-- The exterior differential takes a scalar times a wedge of two exact forms
to the wedge of the three corresponding Kähler differentials. -/
theorem exteriorD2_smul_exact_pair
    (hB : ∀ x i, B.repr (KaehlerDifferential.D L W x) i = D i x)
    (hD : ∀ i j, Function.Commute (D i) (D j)) (a b c : W) :
    exteriorD2 B D (a • exteriorPower.ιMulti W 2 (KaehlerDifferential.D L W ∘ ![b,c])) =
      exteriorPower.ιMulti W 3 (KaehlerDifferential.D L W ∘ ![a,b,c]) := by
  rw [exteriorD2_apply, wedge_three B]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, twoBasis_repr_wedge, Function.comp_apply,
    hB]
  rw [divergence_minors D hD]

/-- The scalar-times-exact-wedge rule determines the derivative of every two-form. -/
theorem exteriorD2_unique (y : Fin 3 → W) (hy : ∀ i, B i = KaehlerDifferential.D L W (y i))
    (hB : ∀ x i, B.repr (KaehlerDifferential.D L W x) i = D i x)
    (hD : ∀ i j, Function.Commute (D i) (D j)) (δ : Form L W 2 →ₗ[L] Form L W 3)
    (hδ : ∀ a b c : W,
      δ (a • exteriorPower.ιMulti W 2 (KaehlerDifferential.D L W ∘ ![b,c])) =
        exteriorPower.ιMulti W 3 (KaehlerDifferential.D L W ∘ ![a,b,c])) :
    δ = exteriorD2 B D := by
  apply LinearMap.ext
  intro η
  calc
    δ η = ∑ i, δ ((twoBasis B).repr η i • twoBasis B i) := by rw [← map_sum, (twoBasis B).sum_repr]
    _ = ∑ i, exteriorD2 B D ((twoBasis B).repr η i • twoBasis B i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : i.removeNth B =
          KaehlerDifferential.D L W ∘ ![y (i.succAbove 0), y (i.succAbove 1)] := by
        funext j
        fin_cases j <;> exact hy _
      rw [twoBasis_apply, hi, hδ, exteriorD2_smul_exact_pair B D hB hD]
    _ = exteriorD2 B D η := by rw [← map_sum, (twoBasis B).sum_repr]

include B in
/-- In rank three the relative Kähler four-forms vanish. -/
theorem fourForm_subsingleton : Subsingleton (Form L W 4) := by
  refine ⟨fun x y => (B.exteriorPower 4).repr.injective (Finsupp.ext fun i => ?_)⟩
  have h := (i : Finset (Fin 3)).card_le_univ
  simp at h

end Coordinates

open CycleQ2IncidenceNormalForm CycleQ2GenericPencilLift CycleQ2GenericWeightedField
  CycleQ2GenericWeightedDifferentials

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)

private abbrev direction := endpointDirection c hc

/-- The genuine relative source three-form on the deformed weighted field. -/
def sourceForm := density c hc • volume (coordinateBasis c hc)

/-- The relative exterior derivative on the original generic weighted chart. -/
def weightedExteriorD := exteriorD2 (coordinateBasis c hc) (parameterDeriv c hc)

theorem weightedExteriorD_exact_pair (a b e : field (direction c hc)) :
    let d := KaehlerDifferential.D (parameterField (direction c hc)) (field (direction c hc))
    weightedExteriorD c hc (a • exteriorPower.ιMulti _ 2 (d ∘ ![b,e])) =
      exteriorPower.ιMulti _ 3 (d ∘ ![a,b,e]) :=
  exteriorD2_smul_exact_pair _ _ (coordinateBasis_repr_D c hc) (parameterDerivs_commute c hc) a b e

/-- The usual algebraic exterior derivative rule uniquely determines this operator
on the actual weighted function field. -/
theorem weightedExteriorD_unique
    (δ : Form (parameterField (direction c hc)) (field (direction c hc)) 2 →ₗ[parameterField (direction c hc)]
      Form (parameterField (direction c hc)) (field (direction c hc)) 3)
    (hδ : ∀ a b e : field (direction c hc),
      let d := KaehlerDifferential.D (parameterField (direction c hc)) (field (direction c hc))
      δ (a • exteriorPower.ιMulti _ 2 (d ∘ ![b,e])) = exteriorPower.ιMulti _ 3 (d ∘ ![a,b,e])) :
    δ = weightedExteriorD c hc :=
  exteriorD2_unique _ _ (coordinate _) (coordinateBasis_apply c hc) (coordinateBasis_repr_D c hc)
    (parameterDerivs_commute c hc) δ hδ

theorem weighted_exact_iff_divergence :
    (∃ η, weightedExteriorD c hc η = sourceForm c hc) ↔
      ∃ v : Fin 3 → field (direction c hc), ∑ j, parameterDeriv c hc j (v j) = density c hc :=
  exact_volume_iff_divergence _ _ _

theorem weighted_divergence_of_exterior_exact
    (h : ∃ η, weightedExteriorD c hc η = sourceForm c hc) :
    ∃ v : Fin 3 → field (direction c hc), ∑ j, parameterDeriv c hc j (v j) = density c hc :=
  (weighted_exact_iff_divergence c hc).mp h

/-- The top relative algebraic de Rham group of the weighted function field.
All three-forms are closed since the fourth exterior power vanishes. -/
abbrev TopDeRham :=
  Form (parameterField (direction c hc)) (field (direction c hc)) 3 ⧸
    LinearMap.range (weightedExteriorD c hc)

/-- The de Rham class of the actual source density in its coordinate volume. -/
def sourceClass : TopDeRham c hc := Submodule.Quotient.mk (sourceForm c hc)

theorem sourceClass_eq_zero_iff :
    sourceClass c hc = 0 ↔ ∃ η, weightedExteriorD c hc η = sourceForm c hc :=
  Submodule.Quotient.mk_eq_zero _

/-- A rational relative two-form primitive on the weighted pencil implies exactness
of the protected hypersurface's original residue form. -/
theorem exact_form_of_weighted_exterior_primitive
    (h : ∃ η, weightedExteriorD c hc η = sourceForm c hc) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA :=
  CycleQ2GenericWeightedFieldTransfer.exact_form_of_weighted_field_primitive c hc
    (weighted_divergence_of_exterior_exact c hc h)

theorem exact_form_of_sourceClass_eq_zero (h : sourceClass c hc = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA :=
  exact_form_of_weighted_exterior_primitive c hc ((sourceClass_eq_zero_iff c hc).mp h)

theorem certificate_of_sourceClass_eq_zero (h : sourceClass c hc = 0) :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (exact_form_of_sourceClass_eq_zero c hc h)

end CycleQ2GenericWeightedExterior
end

#print axioms CycleQ2GenericWeightedExterior.weightedExteriorD_exact_pair
#print axioms CycleQ2GenericWeightedExterior.fourForm_subsingleton
#print axioms CycleQ2GenericWeightedExterior.weightedExteriorD_unique
#print axioms CycleQ2GenericWeightedExterior.weighted_exact_iff_divergence
#print axioms CycleQ2GenericWeightedExterior.exact_form_of_weighted_exterior_primitive
#print axioms CycleQ2GenericWeightedExterior.exact_form_of_sourceClass_eq_zero
#print axioms CycleQ2GenericWeightedExterior.certificate_of_sourceClass_eq_zero
