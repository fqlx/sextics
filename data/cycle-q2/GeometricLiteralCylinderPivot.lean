import Proposal.GeometricCurveCylinderDifferential
import Proposal.GeometricLiteralCylinderAdjunction
import Proposal.GeometricLiteralAbelJacobiSeedLiftChart
import Proposal.GeometricLiteralAbelJacobiSectionRows
import Proposal.GeometricLiteralAbelJacobiContraction
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The differential of the actual single-row curve presentation

After the fixed sextic equation has been imposed, the curve presentation
for a matrix pivot has exactly the cubic and that pivot's section row as
defining equations. The two-conormal numerator therefore descends to its
actual Kähler differentials even when the curve is singular. Inverting
the matrix entry identifies this presentation with the original curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCylinderPivot

open scoped TensorProduct
open CycleQ2CurveCylinderDifferential
  CycleQ2LiteralAbelJacobiSeedLiftChart CycleQ2LiteralAbelJacobiSectionRows
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiEquations CycleQ2IncidencePolynomialJacobianBinding

private abbrev seed := seedPoint (57 : ℂ) Complex.I
variable (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart)
abbrev R := RowRing seed t i p
private abbrev rowIdeal := Ideal.span (Set.range (chartEquations seed t i p))
private abbrev quotient := Ideal.Quotient.mk (fixedIdeal i)
private abbrev rowOnT := quotient i (seedRow t i p.1)
local instance closedCurveRing : CommRing (A t i) := inferInstance
local instance threefoldRing : CommRing (T i) := inferInstance
local instance rowRing : CommRing (R t i p) := inferInstance

private theorem equation_zero : chartEquations seed t i p 0 = seedF i := rfl
private theorem equation_one : chartEquations seed t i p 1 = seedH i := rfl
private theorem equation_two : chartEquations seed t i p 2 = seedRow t i p.1 := rfl

private theorem fixed_le : fixedIdeal i ≤ rowIdeal t i p :=
  (Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.subset_span ⟨0, equation_zero t i p⟩)

/-- Restriction of the fixed-sextic functions to the three-equation presentation
used in the actual matrix-pivot cover. -/
def toRow : T i →+* R t i p := Ideal.Quotient.factor (fixed_le t i p)

local instance scalar : Algebra (T i) (R t i p) := (toRow t i p).toAlgebra
local instance complexTower : IsScalarTower ℂ (T i) (R t i p) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := T i) (A := R t i p) fun _ => rfl

theorem toRow_surjective : Function.Surjective (toRow t i p) := Ideal.Quotient.factor_surjective _

theorem toRow_ker : RingHom.ker (toRow t i p) = Ideal.span {cubicOnT i, rowOnT t i p} := by
  rw [toRow, Ideal.Quotient.factor_ker]
  change (Ideal.span (Set.range (chartEquations seed t i p))).map _ = _
  rw [Ideal.map_span]
  let f := quotient i
  have h0 : f (seedF i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    fin_cases m
    · change f (seedF i) ∈ _
      rw [h0]
      exact Ideal.zero_mem _
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro _ (rfl | h)
    · exact Ideal.subset_span ⟨_, ⟨1, rfl⟩, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp h
      exact Ideal.subset_span ⟨_, ⟨2, rfl⟩, rfl⟩

abbrev Restricted := R t i p ⊗[T i] KaehlerDifferential ℂ (T i)
abbrev Total := R t i p × Restricted t i p

/-- The single-row presentation on the actual pivot carries a unique
adjunction map on its ordinary Kähler differentials. -/
theorem exists_pivot_adjunction :
    ∃! f : KaehlerDifferential ℂ (R t i p) →ₗ[R t i p] ⋀[R t i p]^4 (Total t i p),
      ∀ β : Restricted t i p,
        f (KaehlerDifferential.mapBaseChange ℂ (T i) (R t i p) β) =
        exteriorPower.ιMulti (R t i p) 4 ![((1, 0) : Total t i p),
          (0, ambientD (R t i p) (cubicOnT i)), (0, ambientD (R t i p) (rowOnT t i p)), (0, β)] :=
  exists_adjunction_on_differentials (cubicOnT i) (rowOnT t i p) (toRow_surjective t i p)
    (toRow_ker t i p) (LinearMap.inr (R t i p) (R t i p) (Restricted t i p)) (1, 0)

private abbrev pivotOnT := quotient i (pivotPolynomial seed i p)
abbrev FixedOpen := Localization.Away (pivotOnT i p)
abbrev CurveOpen := Localization.Away
  (CycleQ2LiteralAbelJacobiSeedLiftChart.toCurve seed t i p (rowPivot seed t i p))

local instance curveOpenRing : CommRing (CurveOpen t i p) := inferInstance
local instance openCurveAlgebra : Algebra (A t i) (CurveOpen t i p) :=
  inferInstanceAs (Algebra (A t i) (Localization.Away
    (CycleQ2LiteralAbelJacobiSeedLiftChart.toCurve seed t i p (rowPivot seed t i p))))

private def toRowAlg : T i →ₐ[ℂ] R t i p := IsScalarTower.toAlgHom ℂ (T i) (R t i p)

/-- Localized restriction to the actual seed curve on its matrix-pivot cover. -/
def fixedToCurve : FixedOpen i p →ₐ[ℂ] CurveOpen t i p :=
  (seedPivotEquiv t i p).toAlgHom.comp (Localization.awayMapₐ (toRowAlg t i p) (pivotOnT i p))

local instance localizedAlgebra : Algebra (FixedOpen i p) (CurveOpen t i p) :=
  (fixedToCurve t i p).toRingHom.toAlgebra

local instance localizedTower : IsScalarTower ℂ (FixedOpen i p) (CurveOpen t i p) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := FixedOpen i p) (A := CurveOpen t i p)
    fun c => ((fixedToCurve t i p).commutes c).symm

theorem fixedToCurve_surjective : Function.Surjective (fixedToCurve t i p) :=
  (seedPivotEquiv t i p).surjective.comp
    (IsLocalization.Away.mapₐ_surjective_of_surjective (f := toRowAlg t i p)
      (Aₚ := FixedOpen i p) (Bₚ := Localization.Away ((toRowAlg t i p) (pivotOnT i p)))
      (pivotOnT i p) (toRow_surjective t i p))

theorem fixedToCurve_ker : RingHom.ker (fixedToCurve t i p).toRingHom =
    Ideal.span {algebraMap (T i) (FixedOpen i p) (cubicOnT i),
      algebraMap (T i) (FixedOpen i p) (rowOnT t i p)} := by
  let f := toRow t i p
  let s := pivotOnT i p
  have hk : RingHom.ker (fixedToCurve t i p).toRingHom = RingHom.ker (Localization.awayMap f s) := by
    ext x
    change seedPivotEquiv t i p (Localization.awayMap f s x) = 0 ↔ Localization.awayMap f s x = 0
    exact (seedPivotEquiv t i p).map_eq_zero_iff
  rw [hk, show RingHom.ker (Localization.awayMap f s) =
      (RingHom.ker f).map (algebraMap (T i) (FixedOpen i p)) from
    IsLocalization.ker_map (Localization.Away (f s)) f (Submonoid.map_powers f s),
    show RingHom.ker f = _ from toRow_ker t i p, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]

abbrev OpenRestricted := CurveOpen t i p ⊗[FixedOpen i p] KaehlerDifferential ℂ (FixedOpen i p)
abbrev OpenTotal := CurveOpen t i p × OpenRestricted t i p

/-- The adjunction numerator on the ordinary differentials of an original
localized curve chart. This construction requires no smoothness of the curve. -/
theorem exists_original_pivot_adjunction :
    let Q := FixedOpen i p
    let C := CurveOpen t i p
    let h := algebraMap (T i) Q (cubicOnT i)
    let g := algebraMap (T i) Q (rowOnT t i p)
    ∃! f : KaehlerDifferential ℂ C →ₗ[C] ⋀[C]^4 (OpenTotal t i p),
      ∀ β : OpenRestricted t i p,
        f (KaehlerDifferential.mapBaseChange ℂ Q C β) =
          exteriorPower.ιMulti C 4 ![((1, 0) : OpenTotal t i p),
            (0, ambientD C h), (0, ambientD C g), (0, β)] :=
  exists_adjunction_on_differentials _ _ (fixedToCurve_surjective t i p) (fixedToCurve_ker t i p)
    (LinearMap.inr (CurveOpen t i p) (CurveOpen t i p) (OpenRestricted t i p)) (1, 0)

open CycleQ2CurveCylinderAdjunction CycleQ2LiteralCylinderAdjunction
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceEtaleParameter

/-- The local adjunction map on the actual curve chart. -/
def pivotAdjunction : KaehlerDifferential ℂ (CurveOpen t i p) →ₗ[CurveOpen t i p]
    ⋀[CurveOpen t i p]^4 (OpenTotal t i p) := (exists_original_pivot_adjunction t i p).exists.choose

/-- The fixed-chart mixed covector, localized in the fixed threefold and restricted
along the two defining equations to the actual open curve. -/
def toOpen (z : MixedForms i) : OpenTotal t i p :=
  (fixedToCurve t i p (algebraMap (T i) (FixedOpen i p) z.1),
    (1 : CurveOpen t i p) ⊗ₜ[FixedOpen i p]
      KaehlerDifferential.map ℂ ℂ (T i) (FixedOpen i p) z.2)

private abbrev localCoefficient (b : P) : CurveOpen t i p :=
  fixedToCurve t i p (algebraMap (T i) (FixedOpen i p) (quotient i b))

theorem localCoefficient_eq (b : P) : localCoefficient t i p b =
    algebraMap (A t i) (CurveOpen t i p) (seedChartMap t i b) := by
  change seedPivotEquiv t i p (Localization.awayMap (toRow t i p) (pivotOnT i p)
    (algebraMap (T i) (FixedOpen i p) (quotient i b))) = _
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  exact seedPivotEquiv_algebraMap t i p ((toRow t i p) (quotient i b))

private theorem toOpen_split (b c : P) :
    toOpen t i p ((quotient i c, KaehlerDifferential.D ℂ (T i) (quotient i b)) : MixedForms i) =
      ((0, ambientD (CurveOpen t i p) (algebraMap (T i) (FixedOpen i p) (quotient i b))) : OpenTotal t i p) +
        localCoefficient t i p c • ((1, 0) : OpenTotal t i p) := by
  ext <;> simp [toOpen, ambientD, localCoefficient]

set_option maxHeartbeats 1200000 in
/-- The mixed two-form of the literal moving equations is minus the local
retained cubic times the adjunction image of a genuine curve differential.
The formula holds without any smoothness assumption on that curve. -/
theorem original_mixed_on_differentials (β : OpenRestricted t i p) :
    let Q := FixedOpen i p
    let C := CurveOpen t i p
    let H := toOpen t i p (mixedMap i (KaehlerDifferential.D ℂ Parameters
      (dehomogenizedEquations incidencePoint i 1)))
    let G := toOpen t i p (mixedMap i (KaehlerDifferential.D ℂ Parameters (parameterRow t i p.1)))
    let h := algebraMap (T i) Q (cubicOnT i)
    adjunctionNumerator H G (exteriorPower.ιMulti C 2 ![((0, ambientD C h) : OpenTotal t i p), (0, β)]) =
      -(algebraMap (A t i) (CurveOpen t i p) (seedChartMap t i (tangentL i))) • pivotAdjunction t i p (KaehlerDifferential.mapBaseChange ℂ Q C β) := by
  have hH := congrArg (toOpen t i p) ((mixedMap_D i _).trans (mixed_cubic i))
  have hG := congrArg (toOpen t i p) ((mixedMap_D i _).trans (mixed_row t i p.1))
  dsimp only
  rw [← localCoefficient_eq t i p, hH.trans (toOpen_split t i p (seedH i) (tangentL i)),
    hG.trans (toOpen_split t i p (seedRow t i p.1) (tangentRow t i p.1))]
  refine (moving_conormal_numerator (R := CurveOpen t i p) _ _ _ _ _ _).trans ?_
  exact congrArg (fun z => -localCoefficient t i p (tangentL i) • z)
    (((exists_original_pivot_adjunction t i p).exists.choose_spec β).symm)

end CycleQ2LiteralCylinderPivot
end

#print axioms CycleQ2LiteralCylinderPivot.toRow_ker
#print axioms CycleQ2LiteralCylinderPivot.exists_pivot_adjunction

#print axioms CycleQ2LiteralCylinderPivot.exists_original_pivot_adjunction

#print axioms CycleQ2LiteralCylinderPivot.original_mixed_on_differentials
