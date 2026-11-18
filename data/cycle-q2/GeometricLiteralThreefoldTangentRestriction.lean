import Proposal.GeometricLiteralThreefoldKodairaSpencer

/-!
# Restriction of the fixed threefold's Kodaira–Spencer derivations

The normalized ambient lifts agree on every further Jacobian localization,
including arbitrary fractions. The induced tangent differences commute with
the actual maps of the localized hypersurface rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldTangentRestriction

open CycleQ2LiteralThreefoldKodairaSpencer CycleQ2GeometricSurfaceFirstOrder

def restriction (i : Fin 4) {s t : Finset Index} (hst : s ⊆ t) : Ambient i s →ₐ[P] Ambient i t where
  __ := IsLocalization.Away.lift (S := Ambient i s) (product i s)
    (IsLocalization.Away.isUnit_of_dvd (S := Ambient i t) (product i t)
      (Finset.prod_dvd_prod_of_subset s t (pivot i) hst))
  commutes' a := IsLocalization.Away.lift_eq _ _ a

private theorem inverse_restrict (i : Fin 4) {s t : Finset Index} (hst : s ⊆ t)
    (j : Index) (hj : j ∈ s) :
    restriction i hst (↑((pivot_unit i s j hj).unit⁻¹) : Ambient i s) =
      ↑((pivot_unit i t j (hst hj)).unit⁻¹) := by
  have hu : Units.map (restriction i hst).toMonoidHom (pivot_unit i s j hj).unit =
      (pivot_unit i t j (hst hj)).unit := by
    apply Units.ext
    exact (restriction i hst).commutes (pivot i j)
  exact congrArg (fun u : (Ambient i t)ˣ => (↑(u⁻¹) : Ambient i t)) hu

private theorem lift_restriction_on_polynomial (i : Fin 4) {s t : Finset Index} (hst : s ⊆ t)
    (j : Index) (hj : j ∈ s) (a : P) :
    restriction i hst (lift i s j hj (algebraMap P _ a)) =
      lift i t j (hst hj) (algebraMap P _ a) := by
  change restriction i hst ((localTest i s * _) * (CycleQ2LocalizationDerivation.extend
    (S := Ambient i s) _ (MvPolynomial.pderiv j) (algebraMap P _ a))) =
    (localTest i t * _) * (CycleQ2LocalizationDerivation.extend
      (S := Ambient i t) _ (MvPolynomial.pderiv j) (algebraMap P _ a))
  rw [CycleQ2LocalizationDerivation.extend_map, CycleQ2LocalizationDerivation.extend_map,
    map_mul, map_mul, inverse_restrict i hst j hj, (restriction i hst).commutes,
    (restriction i hst).commutes]

theorem lift_restriction (i : Fin 4) {s t : Finset Index} (hst : s ⊆ t)
    (j : Index) (hj : j ∈ s) (x : Ambient i s) :
    restriction i hst (lift i s j hj x) = lift i t j (hst hj) (restriction i hst x) := by
  let r := restriction i hst
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (product i s)) x
  change x * algebraMap P _ (m : P) = algebraMap P _ a at hm
  have h₁ := congrArg r (congrArg (lift i s j hj) hm)
  have h₂ := congrArg (lift i t j (hst hj)) (congrArg r hm)
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, r, AlgHom.commutes,
    lift_restriction_on_polynomial] at h₁ h₂
  have hu := (IsLocalization.map_units (Ambient i s) m).map r
  rw [AlgHom.commutes] at hu
  exact hu.mul_right_injective (add_left_cancel (h₁.trans h₂.symm))

def closedRestriction (i : Fin 4) {s t : Finset Index} (hst : s ⊆ t) :
    Closed (localF i s) →+* Closed (localF i t) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (restriction i hst).toRingHom) <| by
    change Ideal.span {localF i s} ≤ RingHom.ker _
    refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
    change Ideal.Quotient.mk _ (restriction i hst (localF i s)) = 0
    rw [AlgHom.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem tangent_restriction (i : Fin 4) {s t : Finset Index} (hst : s ⊆ t)
    (j k : Index) (hj : j ∈ s) (hk : k ∈ s) (x : Closed (localF i s)) :
    closedRestriction i hst (tangent i s j k hj hk x) =
      tangent i t j k (hst hj) (hst hk) (closedRestriction i hst x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change closedRestriction i hst (tangentDifference _ _ _ _ (Ideal.Quotient.mk _ a)) =
    tangentDifference _ _ _ _ (Ideal.Quotient.mk _ (restriction i hst a))
  rw [tangentDifference_mk, tangentDifference_mk]
  change Ideal.Quotient.mk _ (restriction i hst (lift i s j hj a - lift i s k hk a)) = _
  rw [map_sub, lift_restriction, lift_restriction]

end CycleQ2LiteralThreefoldTangentRestriction
end

#print axioms CycleQ2LiteralThreefoldTangentRestriction.lift_restriction
#print axioms CycleQ2LiteralThreefoldTangentRestriction.tangent_restriction
