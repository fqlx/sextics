import Proposal.GeometricHodgeEulerTangentAtlas
import Proposal.GeometricHodgeEulerContractionCharts
import Proposal.GeometricHodgeThreefoldSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! The sixteen affine Jacobian opens over any specialization, and the affine
finite nonempty intersections used by the Čech residue complex. Each normal
coordinate equals the indicated normalized derivative of the homogeneous
sextic. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2WeightedResidueAtlas
open CategoryTheory AlgebraicGeometry CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
  CycleQ2HodgeEulerTangentAtlas CycleQ2HodgeEulerContractionCharts
  CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)

abbrev Index := Fin 4 × Fin 4
abbrev normalIndex (a : Index) : Fin 5 := a.1.castSucc.succAbove a.2
abbrev inclusion (i : Fin 4) := (affineChart φ i).inv ≫ (coordinateOpen φ i).ι
abbrev U (a : Index) : (threefold φ).Opens :=
  inclusion φ a.1 ''ᵁ PrimeSpectrum.basicOpen (gradientEntry (F φ a.1) a.2)
abbrev atlas (a : Index) := basicChart (inclusion φ a.1) (gradientEntry (F φ a.1) a.2)

theorem normal_index (a : Index) :
    chartEquiv φ a.1 (gradientRatio φ a.1 (normalIndex a)) =
      gradientEntry (F φ a.1) a.2 := chartEquiv_gradientRatio_succAbove φ a.1 a.2

theorem atlas_overBase (a : Index) : (atlas φ a).inv ≫ (U φ a).ι ≫ toBase φ =
    Spec.map (CommRingCat.ofHom (algebraMap k (Patch (F φ a.1) a.2))) := by
  rw [← Category.assoc, basicChart_inv_ι, Category.assoc]
  change Spec.map _ ≫ ((affineChart φ a.1).inv ≫ (coordinateOpen φ a.1).ι) ≫ toBase φ = _
  rw [Category.assoc,affineChart_overBase,← Spec.map_comp]
  exact congrArg (fun q : k →+* Patch (F φ a.1) a.2 => Spec.map (CommRingCat.ofHom q))
    (IsScalarTower.algebraMap_eq k (CycleQ2HodgeEuler.chart φ a.1) (Patch (F φ a.1) a.2)).symm

theorem inclusion_range (i : Fin 4) : (inclusion φ i).opensRange = coordinateOpen φ i :=
  (Scheme.Hom.opensRange_comp_of_isIso (affineChart φ i).inv (coordinateOpen φ i).ι).trans
    (Scheme.Opens.opensRange_ι _)

theorem cover (hg : IsUnit (φ goodParameter)) : (⨆ a : Index, U φ a) = ⊤ := by
  have h := hg
  rw [goodParameter,map_mul,IsUnit.mul_iff] at h
  have hc (i : Fin 4) : (⨆ j, U φ (i,j)) = coordinateOpen φ i := by
    have htop : (⨆ j, PrimeSpectrum.basicOpen (gradientEntry (F φ i) j)) = ⊤ :=
      PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (chartGradient_span φ h.1 i)
    change (⨆ j, inclusion φ i ''ᵁ PrimeSpectrum.basicOpen _) = _
    rw [← Scheme.Hom.image_iSup,htop,Scheme.Hom.image_top_eq_opensRange,inclusion_range]
  simpa only [iSup_prod,hc] using (coordinateOpens_cover_of_good φ hg :
    (⨆ i, coordinateOpen φ i) = ⊤)

theorem affine (a : Index) : IsAffineOpen (U φ a) :=
  IsAffine.of_isIso (atlas φ a).hom

/-- Every simplex of positive length has an affine open intersection. -/
theorem finite_affine {ι : Type*} [Finite ι] [Nonempty ι] (a : ι → Index) :
    IsAffineOpen (⨅ i, U φ (a i)) := by
  letI : IsProper (toBase φ) := toBase_proper φ
  letI : (threefold φ).IsSeparated := by
    rw [Scheme.isSeparated_iff,← Limits.terminal.comp_from (toBase φ)]
    infer_instance
  exact IsAffineOpen.iInf (fun i => affine φ (a i))

end CycleQ2WeightedResidueAtlas
end

#print axioms CycleQ2WeightedResidueAtlas.cover
#print axioms CycleQ2WeightedResidueAtlas.finite_affine
