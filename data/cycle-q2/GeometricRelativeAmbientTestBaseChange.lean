import Proposal.GeometricFamilyDeformation

/-!
# Base change of the localized ambient-test thickening

The original square-zero deformation of the sextic by a polynomial test
commutes with coefficient specialization on each coordinate open. Both
reduction and extraction of the epsilon coefficient specialize on the
original localized ring, including its denominators.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2RelativeAmbientTestBaseChange

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceCoefficientMap
  CycleQ2GeometricUniversalSurfaceFirstOrder CycleQ2GeometricSurfaceFirstOrder
  CycleQ2GeometricKernelLocalization CycleQ2GeometricProjectorDefect

attribute [local instance] cubicSelfModule cubicOppositeModule cubicCentralScalar cubicSmulCommClass
  surfaceDeformationModule surfaceDeformationCubicModule reducedAlgebra

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
variable (h : FullCubicTailIndex → R) (F : FullSexticTailIndex → R) (T : MvPolynomial (Fin 5) R)
variable (s : Finset (Fin 3))

private abbrev denominator := deformationCoordinate (sexticClass R h F) (testClass R h T) (coordinateClass R h s)

private theorem denominator_map :
    surfaceDeformationMap φ h F T (denominator h F T s) =
      denominator (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s := by
  change surfaceDeformationMap φ h F T (Ideal.Quotient.mk _ (TrivSqZeroExt.inl _)) =
    Ideal.Quotient.mk _ (TrivSqZeroExt.inl _)
  rw [surfaceDeformationMap_mk]
  apply congrArg (Ideal.Quotient.mk _)
  apply TrivSqZeroExt.ext
  · change cubicMap φ h (coordinateClass R h s) = coordinateClass S (fun i => φ (h i)) s
    rw [coordinateClass, cubicMap_testClass, coordinateClass, remainingInclusion, remainingInclusion,
      MvPolynomial.map_rename, map_baseProduct]
  · exact map_zero (cubicMap φ h)

private abbrev toLocal : SurfaceDeformation R h F T →+* LocalSurfaceDeformation R h F T s :=
  @algebraMap (SurfaceDeformation R h F T) (LocalSurfaceDeformation R h F T s)
    (inferInstance : CommSemiring (SurfaceDeformation R h F T))
    (inferInstance : Semiring (LocalSurfaceDeformation R h F T s)) inferInstance


def thickMap :
    LocalSurfaceDeformation R h F T s →+*
      LocalSurfaceDeformation S (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s :=
  IsLocalization.Away.lift (denominator h F T s)
    (S := LocalSurfaceDeformation R h F T s)
    (g := (toLocal (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s).comp (surfaceDeformationMap φ h F T))
    (by rw [RingHom.comp_apply, denominator_map]; exact IsLocalization.Away.algebraMap_isUnit _)

theorem thickMap_base (x : SurfaceDeformation R h F T) :
    thickMap φ h F T s (toLocal h F T s x) =
      toLocal (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s (surfaceDeformationMap φ h F T x) :=
  IsLocalization.Away.lift_eq _ _ x

private theorem red_base (x : SurfaceDeformation R h F T) :
    localSurfaceReduction R h F T s (toLocal h F T s x) =
      algebraMap (SurfaceRing R h F) (SurfaceLocal R h F s) (surfaceReduction R h F T x) := by
  change localClosedSurfaceEquiv R h F T s (localReduction (SurfaceDeformation R h F T)
    (Closed (sexticClass R h F)) (denominator h F T s) (toLocal h F T s x)) = _
  rw [localReduction_base, localClosedSurfaceEquiv_base]
  rfl

theorem thickMap_reduce (x : LocalSurfaceDeformation R h F T s) :
    localSurfaceReduction S (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s
      (thickMap φ h F T s x) = localMap φ h F s (localSurfaceReduction R h F T s x) := by
  have he : (localSurfaceReduction S (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s).comp
      (thickMap φ h F T s) = (localMap φ h F s).comp (localSurfaceReduction R h F T s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator h F T s))
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply, thickMap_base, red_base, localMap_algebraMap, surfaceDeformationMap_reduction]
  exact RingHom.congr_fun he x

variable [Nontrivial R] [Nontrivial S]

theorem thickMap_epsilon (x : SurfaceLocal R h F s) :
    thickMap φ h F T s ((localSurfaceCoefficients R h F T s).epsilon x) =
      (localSurfaceCoefficients S (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s).epsilon
        (localMap φ h F s x) := by
  let k := localSurfaceCoefficients R h F T s
  let k' := localSurfaceCoefficients S (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s
  have h₁ : thickMap φ h F T s (k.epsilon 1) = k'.epsilon 1 := by
    have e := localSurfaceCoefficients_epsilon_base R h F T s (1 : SurfaceRing R h F)
    have e' := localSurfaceCoefficients_epsilon_base S (fun i => φ (h i)) (fun i => φ (F i))
      (MvPolynomial.map φ T) s (1 : SurfaceRing S _ _)
    simp only [map_one] at e e'
    change thickMap φ h F T s ((localSurfaceCoefficients R h F T s).epsilon 1) = _
    rw [e, thickMap_base, surfaceDeformationMap_epsilon, map_one]
    exact e'.symm
  obtain ⟨v, rfl⟩ := localSurfaceReduction_surjective R h F T s x
  have hv := k.mul_epsilon v 1
  have hv' := k'.mul_epsilon (thickMap φ h F T s v) 1
  simp only [mul_one] at hv hv'
  change thickMap φ h F T s (k.epsilon _) = k'.epsilon _
  rw [← hv, map_mul, h₁, hv', thickMap_reduce]

theorem thickMap_coefficient (z : LocalSurfaceDeformation R h F T s) (hz : localSurfaceReduction R h F T s z = 0) :
    (localSurfaceCoefficients S (fun i => φ (h i)) (fun i => φ (F i)) (MvPolynomial.map φ T) s).coefficient
      (thickMap φ h F T s z) (by rw [thickMap_reduce, hz, map_zero]) =
      localMap φ h F s ((localSurfaceCoefficients R h F T s).coefficient z hz) := by
  apply (localSurfaceCoefficients S _ _ _ s).injective
  rw [Coefficients.epsilon_coefficient, ← thickMap_epsilon, Coefficients.epsilon_coefficient]

end CycleQ2RelativeAmbientTestBaseChange
end

#print axioms CycleQ2RelativeAmbientTestBaseChange.thickMap_reduce
#print axioms CycleQ2RelativeAmbientTestBaseChange.thickMap_coefficient
