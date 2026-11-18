import Proposal.ScratchWeightedLocalPresentations
import Proposal.ScratchWeightedConeChartRestrictions

/-! The full homogeneous coefficient identity in the two native restrictions
of the localized cone divisor over a projective chart overlap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedNativeCoefficient
open MvPolynomial CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold
  CycleQ2GenericSexticGradient CycleQ2HodgeEuler CycleQ2WeightedConeChartRestrictions
  CycleQ2WeightedLocalPresentations

variable {k S : Type} [CommRing k] [CommRing S] [Algebra k S]
variable (φ : CoeffRing →+* k) (M : Submonoid (P k))
def polynomials : P k →+* coneDivisor φ M :=
  (Ideal.Quotient.mk _).comp (algebraMap (P k) (Localization M))

variable (i k' : Fin 4) (g : overlap φ i k' →ₐ[k] S)
def transitionUnit : Sˣ :=
  Units.mkOfMulEqOne _ _ (native_pivots_inv φ i k' g)

private theorem native_point : newPoint φ i k' g =
    fun j => (↑(transitionUnit φ i k' g) : S)^geometricWeight j*oldPoint φ i k' g j :=
  funext (native_scale φ i k' g)

theorem new_denominators
    (hM : ∀ q : M, ∃ n : ℕ, (q : P k).IsWeightedHomogeneous geometricWeight n)
    (hx : ∀ m : M, IsUnit (aeval (oldPoint φ i k' g) (m : P k))) :
    ∀ m : M, IsUnit (aeval (newPoint φ i k' g) (m : P k)) := by
  intro m
  rw [native_point φ i k' g]
  exact scaled_units M (algebraMap k S) (oldPoint φ i k' g) (transitionUnit φ i k' g) hM hx m

theorem restriction_polynomial (x : Fin 5 → S) (hx : ∀ m : M, IsUnit (aeval x (m : P k)))
    (hF : aeval x (equation φ) = 0) (p : P k) :
    restrictCone φ M x hx hF (polynomials φ M p) = aeval x p := locality_map M x hx p

/-- This is the scalar identity required by the chart gluing of arbitrary
finite sums of horizontal wedges, for the genuine old and new sections. -/
theorem coefficient_character
    (hx : ∀ m : M, IsUnit (aeval (oldPoint φ i k' g) (m : P k)))
    (hy : ∀ m : M, IsUnit (aeval (newPoint φ i k' g) (m : P k)))
    {d : ℤ} {c : coneDivisor φ M} (h : Represented (polynomials φ M) M d c) :
    newCone φ M i k' g hy c = (↑((transitionUnit φ i k' g)^d) : S) * oldCone φ M i k' g hx c := by
  let e₀ := oldCone φ M i k' g hx
  let e₁ := newCone φ M i k' g hy
  let t := transitionUnit φ i k' g
  have h₀ (p : P k) : e₀ (polynomials φ M p) =
      eval₂Hom (algebraMap k S) (oldPoint φ i k' g) p :=
    restriction_polynomial φ M _ hx _ p
  have h₁ (p : P k) : e₁ (polynomials φ M p) = eval₂Hom (algebraMap k S)
      (fun j => (t:S)^geometricWeight j * oldPoint φ i k' g j) p := by
    rw [← native_point φ i k' g]
    exact restriction_polynomial φ M _ hy _ p
  have hunit (p : P k) (hp : p ∈ M) : IsUnit (e₁ (polynomials φ M p)) := by
    change IsUnit (newCone φ M i k' g hy (polynomials φ M p))
    change IsUnit (restrictCone φ M _ hy _ (polynomials φ M p))
    rw [restriction_polynomial]
    exact hy ⟨p,hp⟩
  exact h.normalize (algebraMap k S) (oldPoint φ i k' g) t
    e₀.toRingHom e₁.toRingHom h₀ h₁ hunit

/-- A coefficient of total degree N on a wedge of coordinate weight W. -/
theorem coefficient_glue_shift
    (hx : ∀ m : M, IsUnit (aeval (oldPoint φ i k' g) (m : P k)))
    (hy : ∀ m : M, IsUnit (aeval (newPoint φ i k' g) (m : P k)))
    {W N : ℕ} {c : coneDivisor φ M}
    (h : Represented (polynomials φ M) M ((N:ℤ) - (W:ℤ)) c) :
    newCone φ M i k' g hy c * g (invPivot φ i k')^W =
      g (invPivot φ i k')^N * oldCone φ M i k' g hx c := by
  let t := transitionUnit φ i k' g
  have hpow : (t^((N:ℤ)-(W:ℤ)) : Sˣ) * t^W = t^N := by
    rw [← zpow_natCast t W, ← zpow_add, sub_add_cancel, zpow_natCast]
  have hv := congrArg (fun u : Sˣ => (u : S)) hpow
  change (↑(t^((N:ℤ)-(W:ℤ))) : S) * (t:S)^W = (t:S)^N at hv
  rw [coefficient_character φ M i k' g hx hy h]
  change ((↑(t^((N:ℤ)-(W:ℤ))) : S) * _) * (t:S)^W = (t:S)^N * _
  rw [mul_right_comm, hv]

theorem coefficient_glue
    (hx : ∀ m : M, IsUnit (aeval (oldPoint φ i k' g) (m : P k)))
    (hy : ∀ m : M, IsUnit (aeval (newPoint φ i k' g) (m : P k)))
    {n : ℕ} {c : coneDivisor φ M} (h : Represented (polynomials φ M) M (-(n : ℤ)) c) :
    newCone φ M i k' g hy c * g (invPivot φ i k')^n = oldCone φ M i k' g hx c := by
  have h' : Represented (polynomials φ M) M (((0:ℕ):ℤ) - (n:ℤ)) c := by simpa using h
  simpa using coefficient_glue_shift φ M i k' g hx hy (N:=0) (W:=n) h'

end CycleQ2WeightedNativeCoefficient
end

#print axioms CycleQ2WeightedNativeCoefficient.coefficient_glue
