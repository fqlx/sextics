import Proposal.GeometricProtectedGenericPencilModel
import Proposal.GeometricProtectedPencilDoubleCover

/-!
# The fixed coordinate ring of the protected generic pencil

This identifies the fixed ring of the actual coordinate sign involution on
the restriction of the protected sextic over the rational function field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2ProtectedGenericPencilQuotient

open MvPolynomial CycleQ2ProtectedGenericPencilModel
open CycleQ2ProtectedPencilDoubleCover (V coverMap beta sign Double quadraticEquiv beta_fixed_iff)

abbrev OrdinaryRing := P ⧸ Ideal.span {restrictProtected HodgeSubmission.F}
abbrev ordinaryQuotient := Ideal.Quotient.mkₐ K (Ideal.span {restrictProtected HodgeSubmission.F} : Ideal P)

private def ordinaryAsCover : OrdinaryRing ≃ₐ[K] V G :=
  Ideal.quotientEquivAlgOfEq K (congrArg (fun p : P => Ideal.span {p}) restrictProtected_F)

/-- The map on homogeneous coordinate rings for the protected pencil. -/
def inclusion : QuotientRing →ₐ[K] OrdinaryRing :=
  ordinaryAsCover.symm.toAlgHom.comp (coverMap G)

theorem inclusion_quotient (p : P) : inclusion (quotient p) = ordinaryQuotient (square p) := rfl

def ordinarySign : OrdinaryRing →ₐ[K] OrdinaryRing :=
  ordinaryAsCover.symm.toAlgHom.comp ((beta G).comp ordinaryAsCover.toAlgHom)

theorem ordinarySign_quotient (p : P) :
    ordinarySign (ordinaryQuotient p) = ordinaryQuotient (sign p) := rfl

/-- The ordinary coordinate algebra of F at the generic pencil parameter
has one even and one odd summand over the weighted coordinate ring. -/
def protectedQuadraticEquiv : OrdinaryRing ≃ₐ[K] Double G :=
  ordinaryAsCover.trans ((quadraticEquiv G).restrictScalars K)

instance protectedCoverAlgebra : Algebra QuotientRing OrdinaryRing := inclusion.toRingHom.toAlgebra

private def ordinaryAsCoverOver : OrdinaryRing ≃ₐ[QuotientRing] V G where
  __ := ordinaryAsCover.toRingEquiv
  commutes' r := ordinaryAsCover.apply_symm_apply (coverMap G r)

/-- The structural map of the protected cones is finite free of rank two. -/
def protectedCoverBasis : Module.Basis (Fin 2) QuotientRing OrdinaryRing :=
  (CycleQ2ProtectedPencilDoubleCover.coverBasis G).map ordinaryAsCoverOver.symm.toLinearEquiv

theorem protectedCover_finite : Module.Finite QuotientRing OrdinaryRing :=
  Module.Finite.of_basis protectedCoverBasis

/-- An ordinary homogeneous-coordinate-ring element descends uniquely
through w = u² exactly when the original paired sign fixes it. -/
theorem ordinary_fixed_iff (x : OrdinaryRing) :
    ordinarySign x = x ↔ ∃! y : QuotientRing, inclusion y = x := by
  have h (y : QuotientRing) : inclusion y = x ↔ coverMap G y = ordinaryAsCover x :=
    ordinaryAsCover.symm_apply_eq
  have hs : ordinarySign x = x ↔ beta G (ordinaryAsCover x) = ordinaryAsCover x :=
    ordinaryAsCover.symm_apply_eq
  rw [hs, beta_fixed_iff]
  exact existsUnique_congr (fun y => (h y).symm)

abbrev fixedRing := AlgHom.equalizer ordinarySign (AlgHom.id K OrdinaryRing)

/-- The β-fixed coordinate algebra of the protected generic fibre is
the weighted hypersurface's homogeneous coordinate algebra. -/
def weightedEquivFixed : QuotientRing ≃ₐ[K] fixedRing := by
  let i : QuotientRing →ₐ[K] fixedRing := inclusion.codRestrict fixedRing fun y =>
    (ordinary_fixed_iff (inclusion y)).mpr ⟨y, rfl, fun z hz =>
      CycleQ2ProtectedPencilDoubleCover.coverMap_injective G (ordinaryAsCover.symm.injective hz)⟩
  apply AlgEquiv.ofBijective i
  constructor
  · intro x y h
    apply CycleQ2ProtectedPencilDoubleCover.coverMap_injective G
    exact ordinaryAsCover.symm.injective (congrArg Subtype.val h)
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,_⟩ := (ordinary_fixed_iff x).mp hx
    exact ⟨y, Subtype.ext hy⟩

open CycleQ2SeedCyclicAction

/-- The second action fixes the pencil coordinate u and therefore commutes
with the substitution w = u². -/
theorem gamma_square (z : K) : (polynomialAction z).comp square = square.comp (polynomialAction z) := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j <;> simp [square, actionValues]

def ordinaryGamma (z : K) (hz : z^3 = 1) : OrdinaryRing →ₐ[K] OrdinaryRing :=
  CycleQ2ProtectedPencilDoubleCover.descend (restrictProtected HodgeSubmission.F)
    (ordinaryQuotient.comp (polynomialAction z)) (by
      have he : polynomialAction z (restrictProtected HodgeSubmission.F) = restrictProtected HodgeSubmission.F := by
        rw [restrictProtected_F]
        exact (AlgHom.congr_fun (gamma_square z) G).trans (congrArg square (G_gamma z hz))
      change ordinaryQuotient (polynomialAction z (restrictProtected HodgeSubmission.F)) = 0
      rw [he]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

theorem inclusion_gamma (z : K) (hz : z^3 = 1) (x : QuotientRing) :
    ordinaryGamma z hz (inclusion x) = inclusion (gammaCone z hz x) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg ordinaryQuotient (AlgHom.congr_fun (gamma_square z) p)

end CycleQ2ProtectedGenericPencilQuotient
end

#print axioms CycleQ2ProtectedGenericPencilQuotient.protectedQuadraticEquiv
#print axioms CycleQ2ProtectedGenericPencilQuotient.protectedCoverBasis
#print axioms CycleQ2ProtectedGenericPencilQuotient.ordinary_fixed_iff

#print axioms CycleQ2ProtectedGenericPencilQuotient.weightedEquivFixed

#print axioms CycleQ2ProtectedGenericPencilQuotient.inclusion_gamma
