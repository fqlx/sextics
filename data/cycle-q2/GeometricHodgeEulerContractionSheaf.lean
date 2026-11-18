import Proposal.GeometricLiteralThreefoldDifferentialFrame
import Proposal.GeometricHodgeEulerContractionRestriction
import Proposal.GeometricChartTangentMaps

/-!
# Interior multiplication on the genuine exterior sheaves

A vector field on an open is an actual local morphism from the cotangent
sheaf to the structure sheaf. Its evaluation is compatible with restriction,
so contraction descends from exterior powers of sections to exterior sheaves.
On an affine chart it agrees with contraction of the original Kähler forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerContractionSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricIntrinsicNormal CycleQ2LocalSheafificationFrame
  CycleQ2GeometricExteriorLocalFrames CycleQ2LiteralThreefoldResidueContraction

variable {X : Scheme.{0}} (M : SheafOfModules.{0} (ringSheaf X.sheaf))

abbrev form (n : ℕ) := exteriorSheaf X.sheaf M.val n
abbrev dual := moduleHomSheaf X.sheaf M (SheafOfModules.unit (ringSheaf X.sheaf))

private abbrev raw := exteriorPresheaf X.sheaf.obj M.val 3
private abbrev present := toExteriorSheaf X.sheaf M.val 3

variable (U : X.Opens) (δ : (dual M).val.obj (op U))

private abbrev presentation := @overPresentation (show TopCat from X)
  (ringSheaf X.sheaf) (raw M) U (form M 3) (present M)

local instance presentationInjective :
    PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      (presentation M U) :=
  @overPresentation_locallyInjective (show TopCat from X) (ringSheaf X.sheaf) (raw M) U (form M 3)
    (present M) (exteriorPresentation_locallyInjective X.sheaf M.val 3)

local instance presentationSurjective :
    PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      (presentation M U) :=
  @overPresentation_locallySurjective (show TopCat from X) (ringSheaf X.sheaf) (raw M) U (form M 3)
    (present M) (exteriorPresentation_locallySurjective X.sheaf M.val 3)

def evaluateOn (V : Over U) : M.val.obj (op V.left) →ₗ[Γ(X,V.left)] Γ(X,V.left) where
  toFun := δ.val.app (op V)
  map_add' x y := (δ.val.app (op V)).hom.map_add x y
  map_smul' x y := δ.property V x y

private def rawAt (V : Over U) :
    (⋀[Γ(X,V.left)]^3 (M.val.obj (op V.left))) →ₗ[Γ(X,V.left)] (form M 2).val.obj (op V.left) :=
  (exteriorSection X.sheaf M.val 2 V.left).comp
    (CycleQ2LiteralThreefoldResidueContraction.interior (R := Γ(X,V.left)) 2 (evaluateOn M U δ V))

private def rawContract :
    overPresheaf (ringSheaf X.sheaf) (raw M) U ⟶ ((form M 2).over U).val where
  app V := ModuleCat.ofHom (rawAt M U δ V.unop)
  naturality {V W} f := by
    apply ConcreteCategory.hom_ext
    intro x
    change exteriorSection X.sheaf M.val 2 W.unop.left
      (interior 2 (evaluateOn M U δ W.unop) (exteriorMap (X.presheaf.map f.unop.left.op).hom
        (M.val.restrictₛₗ f.unop.left.op) 3 x)) =
      (form M 2).val.map f.unop.left.op (exteriorSection X.sheaf M.val 2 V.unop.left
        (interior 2 (evaluateOn M U δ V.unop) x))
    rw [exteriorSection_restrict]
    apply congrArg
    apply interior_natural
    intro z
    exact ConcreteCategory.congr_hom (δ.val.naturality f) z

/-- Actual morphism of module sheaves on the over-site of the open. -/
def contractOver : (form M 3).over U ⟶ (form M 2).over U where
  val := (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation M U) ((form M 2).over U).isSheaf).symm (rawContract M U δ)

theorem contractOver_exterior (V : Over U)
    (x : ⋀[Γ(X,V.left)]^3 (M.val.obj (op V.left))) :
    (contractOver M U δ).val.app (op V) (exteriorSection X.sheaf M.val 3 V.left x) =
      exteriorSection X.sheaf M.val 2 V.left (interior 2 (evaluateOn M U δ V) x) := by
  have h := (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation M U) ((form M 2).over U).isSheaf).apply_symm_apply (rawContract M U δ)
  exact congrArg (fun f : overPresheaf (ringSheaf X.sheaf) (raw M) U ⟶ ((form M 2).over U).val =>
    f.app (op V) x) h

def contractSection : (form M 3).val.obj (op U) →ₗ[Γ(X,U)] (form M 2).val.obj (op U) :=
  ((contractOver M U δ).val.app (op (Over.mk (𝟙 U)))).hom

theorem contractSection_exterior (x : ⋀[Γ(X,U)]^3 (M.val.obj (op U))) :
    contractSection M U δ (exteriorSection X.sheaf M.val 3 U x) =
      exteriorSection X.sheaf M.val 2 U (interior 2 (evaluateOn M U δ (Over.mk (𝟙 U))) x) :=
  contractOver_exterior M U δ (Over.mk (𝟙 U)) x

private def localInterior : LocalLinearHom X.sheaf (form M 3) (form M 2) U :=
  (localLinearHomEquiv X.sheaf (form M 3) (form M 2) U).symm (contractOver M U δ)

private theorem localInterior_restrict {V : X.Opens} (f : V ⟶ U) :
    restrictLocalLinearHom X.sheaf (form M 3) (form M 2) f.op (localInterior M U δ) =
      localInterior M V ((dual M).val.map f.op δ) := by
  apply (localLinearHomEquiv X.sheaf (form M 3) (form M 2) V).injective
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation M V) ((form M 2).over V).isSheaf).injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro x
  let W' : Over U := Over.mk (W.unop.hom ≫ f)
  change (contractOver M U δ).val.app (op W') (exteriorSection X.sheaf M.val 3 W.unop.left x) =
    (contractOver M V ((dual M).val.map f.op δ)).val.app W (exteriorSection X.sheaf M.val 3 W.unop.left x)
  exact (contractOver_exterior M U δ W' x).trans
    (contractOver_exterior M V ((dual M).val.map f.op δ) W.unop x).symm

theorem contractSection_restrict {V : X.Opens} (h : V ≤ U) (ω : (form M 3).val.obj (op U)) :
    (form M 2).val.map (homOfLE h).op (contractSection M U δ ω) =
      contractSection M V ((dual M).val.map (homOfLE h).op δ) ((form M 3).val.map (homOfLE h).op ω) := by
  have hn := localLinearHomEvaluate_restrict X.sheaf (form M 3) (form M 2)
    (homOfLE h) (localInterior M U δ) ω
  rw [localInterior_restrict] at hn
  exact hn.symm

section Chart
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialRestriction
  CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricChartTangentMaps CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality
open scoped KaehlerDifferential
variable {O : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : O.toScheme ≅ Spec (CommRingCat.of A)) (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ O.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

theorem contractSection_chart (v : Derivation ℂ A A) (ω : ⋀[A]^3 Ω[A⁄ℂ]) :
    contractSection (differentialSheaf X.sheaf (schemeCoefficient f)) O (tangentSection e f h v)
      (chartExteriorSheafSection e f h 3 (chartTop O) ω) =
      chartExteriorSheafSection e f h 2 (chartTop O) (interior 2 v.liftKaehlerDifferential ω) := by
  let N := differentialSheaf X.sheaf (schemeCoefficient f)
  let g := chartSection e (chartTop O)
  let L := sectionLiftSemilinear X.sheaf (schemeCoefficient f) N
    (universalDifferential X.sheaf (schemeCoefficient f)) O g (chartSection_complex e f h (chartTop O))
  change contractSection N O (tangentSection e f h v) (exteriorSection X.sheaf N.val 3 O (exteriorMap g L 3 ω)) =
    exteriorSection X.sheaf N.val 2 O (exteriorMap g L 2 (interior 2 v.liftKaehlerDifferential ω))
  rw [contractSection_exterior]
  apply congrArg
  exact interior_natural g L v.liftKaehlerDifferential _ (tangentSection_on_form e f h v) 2 ω

open CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerContractionRestriction CycleQ2GenericSexticGradient

/-- The native contraction of the moving family's Poincaré residue, with the
original tangent vector and two-form transported through the same affine chart. -/
theorem contractSection_family (φ : CoeffRing →+* ℂ) (i j : Fin 4)
    (e : O.toScheme ≅ Spec (CommRingCat.of (Patch (CycleQ2HodgeEuler.F φ i) j)))
    (h : e.inv ≫ O.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ (Patch (CycleQ2HodgeEuler.F φ i) j))))
    (v : Derivation ℂ (Patch (CycleQ2HodgeEuler.F φ i) j) (Patch (CycleQ2HodgeEuler.F φ i) j)) :
    contractSection (differentialSheaf X.sheaf (schemeCoefficient f)) O (tangentSection e f h v)
      (chartExteriorSheafSection e f h 3 (chartTop O) (projectiveResidue (CycleQ2HodgeEuler.F φ i) i j)) =
      chartExteriorSheafSection e f h 2 (chartTop O) (familyContraction φ i j v) := by
  rw [contractSection_chart, familyContraction_apply]

end Chart
end CycleQ2HodgeEulerContractionSheaf
end

#print axioms CycleQ2HodgeEulerContractionSheaf.contractOver_exterior
#print axioms CycleQ2HodgeEulerContractionSheaf.contractSection_restrict
#print axioms CycleQ2HodgeEulerContractionSheaf.contractSection_chart

#print axioms CycleQ2HodgeEulerContractionSheaf.contractSection_family
