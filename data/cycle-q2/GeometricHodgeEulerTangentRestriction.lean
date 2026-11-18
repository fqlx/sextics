import Proposal.GeometricHodgeEulerTangentSheaf
import Proposal.GeometricSurfaceOverlap
import Proposal.GeometricHodgeEulerOverlap

/-!
# Restriction of the original tangent sheaf on affine charts

On an inclusion of affine charts, the recovered derivation differentiates
the restrictions of the original functions. On every principal subopen it
is exactly the algebraic localization of the original derivation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerTangentSheaf

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricPrincipalChartSections
  CycleQ2GeometricChartTangentMaps

variable {X : Scheme.{0}} {U W : X.Opens} {A B : Type}
  [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (eW : W.toScheme ≅ Spec (CommRingCat.of B))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  (hW : eW.inv ≫ W.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))
  (hWU : W ≤ U) (g : A →+* B)
  (hc : eW.inv ≫ W.ι = Spec.map (CommRingCat.ofHom g) ≫ e.inv ≫ U.ι)

include hc in
omit [Algebra ℂ A] [Algebra ℂ B] in
theorem functions_restrict (a : A) :
    X.presheaf.map (homOfLE hWU).op (functions e a) = functions eW (g a) := by
  rw [functions_apply, functions_apply]
  let V : Over U := Over.mk ((chartTop W).hom ≫ homOfLE hWU)
  exact (chartSection_naturality e (toChartTop V) a).trans
    (chartSection_compatible e eW hWU g hc (chartTop W) a).symm

include hW h hc in
theorem recover_restriction (s : Γ(tangent f,U)) (a : A) :
    recover eW f hW ((tangent f).val.map (homOfLE hWU).op s) (g a) =
      g (recover e f h s a) := by
  apply (functions eW).injective
  rw [recover_apply, ← functions_restrict e eW hWU g hc, recover_apply]
  let D := universalDifferential X.sheaf (schemeCoefficient f)
  have hd : (cotangent f).val.map (homOfLE hWU).op (differential e f a) =
      differential eW f (g a) := by
    change (cotangent f).val.map (homOfLE hWU).op
        (D.d (chartSection e (chartTop U) a)) = D.d (chartSection eW (chartTop W) (g a))
    rw [← functions_apply, ← functions_apply, ← functions_restrict e eW hWU g hc]
    exact (D.d_map (homOfLE hWU).op _).symm
  rw [← hd]
  exact localLinearHomEvaluate_restrict X.sheaf (cotangent f) (functionsModule X) (homOfLE hWU) s _

/-- On a principal subopen the ordinary algebraic localization of a
derivation is the actual restriction map of the intrinsic tangent sheaf. -/
theorem recover_principal (z : A) (s : Γ(tangent f,U)) :
    recover (principalChart e z) f (principalChart_overComplex e z f h)
        ((tangent f).val.map (homOfLE (principalOpen_le e z)).op s) =
      CycleQ2LocalizationDerivation.extend (S := Localization.Away z)
        (Submonoid.powers z) (recover e f h s) := by
  apply CycleQ2LocalizationDerivation.extend_unique
  intro a
  exact recover_restriction e (principalChart e z) f h (principalChart_overComplex e z f h)
    (principalOpen_le e z) (algebraMap A (Localization.Away z)) (principalChart_inv_ι e z) s a

theorem tangentSection_principal (z : A) (D : Derivation ℂ A A) :
    (tangent f).val.map (homOfLE (principalOpen_le e z)).op (tangentSection e f h D) =
      tangentSection (principalChart e z) f (principalChart_overComplex e z f h)
        (CycleQ2LocalizationDerivation.extend (S := Localization.Away z) (Submonoid.powers z) D) := by
  apply (affineTangentEquiv (principalChart e z) f (principalChart_overComplex e z f h)).symm.injective
  change recover _ _ _ _ = (affineTangentEquiv _ _ _).symm ((affineTangentEquiv _ _ _) _)
  rw [Equiv.symm_apply_apply, recover_principal e f h z]
  exact congrArg _ ((affineTangentEquiv e f h).left_inv D)

end CycleQ2HodgeEulerTangentSheaf
end

#print axioms CycleQ2HodgeEulerTangentSheaf.recover_restriction
#print axioms CycleQ2HodgeEulerTangentSheaf.tangentSection_principal
