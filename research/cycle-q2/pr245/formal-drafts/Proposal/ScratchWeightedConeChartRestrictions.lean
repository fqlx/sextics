import Proposal.GeometricHodgeEulerOverlapBinding

/-! Restrict the localized sextic cone and its forms to the two actual projective sections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeChartRestrictions
open MvPolynomial
open CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeEuler CycleQ2GenericSexticGradient

variable {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
abbrev P (A : Type) [CommRing A] := MvPolynomial (Fin 5) A

/-- The normalized coordinate functions on each native hypersurface chart annihilate the
homogeneous sextic under any further restriction of the chart. -/
theorem normalized_equation (φ : CoeffRing →+* A) (i : Fin 4) (g : chart φ i →ₐ[A] S) :
    aeval (g ∘ coordinate φ i) (equation φ) = 0 := by
  have e : aeval (g ∘ coordinate φ i) = (g.comp (chartMap φ i)).comp (dehom i) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [aeval_X]
    rfl
  rw [e]
  change g (chartMap φ i (F φ i)) = 0
  rw [chartMap_F, map_zero]

variable (φ : CoeffRing →+* A) (M : Submonoid (P A))
abbrev coneDivisor := Localization M ⧸ Ideal.span {algebraMap (P A) (Localization M) (equation φ)}

def locality (x : Fin 5 → S) (hx : ∀ m : M, IsUnit (aeval x (m : P A))) :
    Localization M →ₐ[A] S := IsLocalization.liftAlgHom (f := aeval x) hx

@[simp] theorem locality_map (x : Fin 5 → S) (hx : ∀ m : M, IsUnit (aeval x (m : P A))) (p : P A) :
    locality M x hx (algebraMap (P A) (Localization M) p) = aeval x p := IsLocalization.lift_eq hx p

/-- Evaluate the true cone divisor after inverting precisely the denominators of the cone cochain. -/
def restrictCone (x : Fin 5 → S) (hx : ∀ m : M, IsUnit (aeval x (m : P A)))
    (hF : aeval x (equation φ) = 0) : coneDivisor φ M →ₐ[A] S :=
  Ideal.Quotient.liftₐ _ (locality M x hx) ((Ideal.span_singleton_le_iff_mem _).mpr
    (show locality M x hx (algebraMap (P A) (Localization M) (equation φ)) = 0 from
      (locality_map M x hx _).trans hF))

def coord (j : Fin 5) : coneDivisor φ M :=
  Ideal.Quotient.mk _ (algebraMap (P A) (Localization M) (X j))

@[simp] theorem restrictCone_coord (x : Fin 5 → S) (hx : ∀ m : M, IsUnit (aeval x (m : P A)))
    (hF : aeval x (equation φ) = 0) (j : Fin 5) :
    restrictCone φ M x hx hF (coord φ M j) = x j := by
  change locality M x hx (algebraMap (P A) (Localization M) (X j)) = _
  rw [locality_map, aeval_X]

/-- All homomorphisms out of the localized cone divisor are determined by
the five ambient coordinates. This also applies on higher intersections. -/
theorem cone_hom_ext (f g : coneDivisor φ M →ₐ[A] S)
    (h : ∀ j, f (coord φ M j) = g (coord φ M j)) : f = g := by
  apply Ideal.Quotient.algHom_ext A
  apply IsLocalization.algHom_ext M
  apply MvPolynomial.algHom_ext
  exact h

theorem restrictCone_comp {T : Type} [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (x : Fin 5 → S) (hx : ∀ m : M, IsUnit (aeval x (m : P A))) (hF : aeval x (equation φ) = 0)
    (hy : ∀ m : M, IsUnit (aeval (f ∘ x) (m : P A)))
    (hF' : aeval (f ∘ x) (equation φ) = 0) :
    f.comp (restrictCone φ M x hx hF) = restrictCone φ M (f ∘ x) hy hF' := by
  apply cone_hom_ext φ M
  intro j
  simp only [AlgHom.comp_apply, restrictCone_coord, Function.comp_apply]

variable (i k : Fin 4) (g : overlap φ i k →ₐ[A] S)
abbrev oldSections : chart φ i →ₐ[A] S := g.comp (IsScalarTower.toAlgHom A _ _)
abbrev newSections : chart φ k →ₐ[A] S := g.comp (overlapMap φ i k)
abbrev oldPoint := oldSections φ i k g ∘ coordinate φ i
abbrev newPoint := newSections φ i k g ∘ coordinate φ k

/-- Actual transition function on any ring receiving the affine overlap, with its inverse exhibited. -/
theorem native_pivots_inv : g (invPivot φ i k) * g (localCoordinate φ i k k.castSucc) = 1 := by
  rw [← map_mul, mul_comm, localCoordinate_mul_invPivot, map_one]

theorem native_scale (j : Fin 5) :
    newPoint φ i k g j = g (invPivot φ i k)^(geometricWeight j) * oldPoint φ i k g j := by
  change g (overlapMap φ i k (coordinate φ k j)) =
    g (invPivot φ i k)^(geometricWeight j) * g (localCoordinate φ i k j)
  rw [overlapMap_coordinate, ratioCoordinate, map_mul, map_pow]

def oldCone (hx : ∀ m : M, IsUnit (aeval (oldPoint φ i k g) (m : P A))) :
    coneDivisor φ M →ₐ[A] S := restrictCone φ M _ hx (normalized_equation φ i _)

def newCone (hy : ∀ m : M, IsUnit (aeval (newPoint φ i k g) (m : P A))) :
    coneDivisor φ M →ₐ[A] S := restrictCone φ M _ hy (normalized_equation φ k _)

theorem cone_coord_scale (hx : ∀ m : M, IsUnit (aeval (oldPoint φ i k g) (m : P A)))
    (hy : ∀ m : M, IsUnit (aeval (newPoint φ i k g) (m : P A))) (j : Fin 5) :
    newCone φ M i k g hy (coord φ M j) = g (invPivot φ i k)^(geometricWeight j) *
      oldCone φ M i k g hx (coord φ M j) := by
  simpa only [oldCone,newCone,restrictCone_coord] using native_scale φ i k g j

end CycleQ2WeightedConeChartRestrictions
end
#print axioms CycleQ2WeightedConeChartRestrictions.cone_coord_scale
