import Proposal.GeometricLiteralMovingPivotPrincipal
import Proposal.GeometricLocalizedDerivations

/-!
# Localized derivations evaluate in the actual cotangent sheaf

The native Kodaira–Spencer derivation on a principal subopen computes
the true tangent evaluation on every further subopen and on every
logarithmic differential in the localized ring.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingPivotDifferential

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafLocalIso
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeTangentEvaluation
  CycleQ2LiteralNativeChernCocycle CycleQ2LiteralNativeKodairaSpencerCocycle
  CycleQ2LiteralSheafChernKodairaSpencerCup CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralMovingPivotPrincipal
  CycleQ2GeometricLocalizedDerivations CycleQ2GeometricSquareZeroSplittings

attribute [local instance] CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule

private theorem fraction_ext {A B T : Type} [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] (S : Submonoid A) [IsLocalization S B] (m : B →+* T) (f g : B → T)
    (hf : ∀ x y, f (x*y) = m x * f y + m y * f x)
    (hg : ∀ x y, g (x*y) = m x * g y + m y * g x)
    (hb : ∀ a : A, f (algebraMap A B a) = g (algebraMap A B a)) (x : B) : f x = g x := by
  obtain ⟨⟨a,d⟩, hx⟩ := IsLocalization.surj S x
  have hf' := congrArg f hx
  have hg' := congrArg g hx
  rw [hf, hb, hb] at hf'
  rw [hg] at hg'
  exact ((IsLocalization.map_units B d).map m).mul_left_cancel (add_left_cancel (hf'.trans hg'.symm))

variable (s : Finset Vertex) (hs : s.Nonempty) (q : ClosedRing s)
  (W : Surface.Opens) (hW : W ≤ principalOpen s hs q)

def value : Localization.Away q →+* Γ(Surface,W) :=
  (Surface.presheaf.map (homOfLE hW).op).hom.comp (closedPrincipalEquiv s hs q).toRingHom

theorem value_base (x : ClosedRing s) :
    value s hs q W hW (algebraMap (ClosedRing s) (Localization.Away q) x) =
      Surface.presheaf.map (homOfLE (hW.trans (principalOpen_le s hs q))).op (closedSectionsEquiv s hs x) := by
  change Surface.presheaf.map (homOfLE hW).op (closedPrincipalEquiv s hs q
    (algebraMap (ClosedRing s) (Localization.Away q) x)) = _
  rw [closedPrincipalEquiv_base]
  exact CycleQ2GeometricSheafLocalIso.res_comp CycleQ2LiteralNativeGaugeSections.coefficientSheaf _ _ _

private abbrev d (O : Surface.Opens) :=
  (universalDifferential Surface.sheaf globalCoefficient).d (X := op O)

variable (δ : Derivation ℂ (ClosedRing s) (ClosedRing s))

private abbrev T := res tangentAddSheaf (hW.trans (principalOpen_le s hs q)) (nativeTangent s hs δ)

theorem value_derivative_base (a : ClosedRing s) :
    evaluateTangent W (T s hs q W hW δ) (d W (value s hs q W hW (algebraMap _ _ a))) =
      value s hs q W hW (algebraMap _ _ (δ a)) := by
  let h := hW.trans (principalOpen_le s hs q)
  rw [value_base, value_base]
  let da := KaehlerDifferential.D ℂ (ClosedRing s) a
  have hd : d W (Surface.presheaf.map (homOfLE h).op (nativeSectionsAlgEquiv s hs a)) =
      res differentialAddSheaf h (nativeFormToSheaf s hs da) := by
    rw [show da = KaehlerDifferential.D ℂ (ClosedRing s) a from rfl, nativeFormToSheaf_D]
    exact (universalDifferential Surface.sheaf globalCoefficient).d_map (homOfLE h).op _
  have he : evaluateTangent (closedOpen s) (nativeTangent s hs δ) (nativeFormToSheaf s hs da) =
      nativeSectionsAlgEquiv s hs (δ a) :=
    (nativeTangent_on_form s hs δ da).trans (congrArg (nativeSectionsAlgEquiv s hs)
      (Derivation.liftKaehlerDifferential_comp_D δ a))
  exact (congrArg (evaluateTangent W (T s hs q W hW δ)) hd).trans
    ((evaluateTangent_restrict h (nativeTangent s hs δ) (nativeFormToSheaf s hs da)).trans
      (congrArg (res CycleQ2LiteralNativeGaugeSections.coefficientSheaf h) he))

/-- On all fractions the actual sheaf tangent is the localized derivation. -/
theorem value_derivative (x : Localization.Away q) :
    evaluateTangent W (T s hs q W hW δ) (d W (value s hs q W hW x)) =
      value s hs q W hW (localizedDerivation (Submonoid.powers q) (Localization.Away q) δ x) := by
  let m := value s hs q W hW
  let g := localizedDerivation (Submonoid.powers q) (Localization.Away q) δ
  apply fraction_ext (Submonoid.powers q) m (fun y => evaluateTangent W (T s hs q W hW δ) (d W (m y))) (fun y => m (g y))
  · intro y z
    dsimp only
    rw [map_mul, (universalDifferential Surface.sheaf globalCoefficient).d_mul, map_add, map_smul, map_smul] <;> rfl
  · intro y z
    dsimp only
    rw [g.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  · intro a
    dsimp only
    rw [show g (algebraMap (ClosedRing s) (Localization.Away q) a) = algebraMap _ _ (δ a)
      from localizedDerivation_algebraMap _ _ _ _]
    exact value_derivative_base s hs q W hW δ a

theorem value_log (g : (Localization.Away q)ˣ) :
    evaluateTangent W (T s hs q W hW δ)
        (sheafLogDifferential W (Units.map (value s hs q W hW).toMonoidHom g)) =
      value s hs q W hW ((localizedDerivation (Submonoid.powers q) (Localization.Away q) δ).liftKaehlerDifferential
        (logDifferential (K := ℂ) g)) := by
  let m := value s hs q W hW
  let δ' := localizedDerivation (Submonoid.powers q) (Localization.Away q) δ
  change evaluateTangent W _ ((↑((Units.map m.toMonoidHom g)⁻¹) : Γ(Surface,W)) • d W (m (g : Localization.Away q))) =
    m (δ'.liftKaehlerDifferential ((↑(g⁻¹) : Localization.Away q) • KaehlerDifferential.D ℂ _ (g : Localization.Away q)))
  have hu : (↑((Units.map m.toMonoidHom g)⁻¹) : Γ(Surface,W)) = m (↑(g⁻¹) : Localization.Away q) := rfl
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, Derivation.liftKaehlerDifferential_comp_D,
    hu, value_derivative]

end CycleQ2LiteralMovingPivotDifferential
end

#print axioms CycleQ2LiteralMovingPivotDifferential.value_derivative
#print axioms CycleQ2LiteralMovingPivotDifferential.value_log
