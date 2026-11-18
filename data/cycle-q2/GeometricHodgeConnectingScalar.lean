import Proposal.GeometricCartierDeformation
import Proposal.GeometricOpenCoverAdditiveExactness

/-!
# Complex linearity of the coefficient connecting morphism

Scalar multiplication on the three original module sheaves defines an
endomorphism of their underlying short exact sequence. Naturality of the
Yoneda extension makes the connecting map complex linear on every open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeConnectingScalar

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2GeometricOpenCoverAdditiveExactness (additiveComplex)
open CycleQ2GeometricSheafCohomologyScalar
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricConeCech.HZero (sectionsEquiv)

variable {X : Scheme.{0}} (c : ℂ →+* Γ(X,⊤)) (S : ShortComplex X.Modules)
local instance (Y : TopCat.{0}) : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} Y) := HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

open CycleQ2GeometricIntrinsicCartierCohomology (openConnecting openConnecting_naturality moduleScalarComplexEnd)

@[instance_reducible] def sectionModule (M : X.Modules) (V : X.Opens) : Module ℂ Γ(M,V) := by
  let f : ℂ →+* Γ(X,V) := coefficientOn X.sheaf c V
  exact Module.compHom Γ(M,V) f

def sectionBoundary (hs : (additiveComplex S).ShortExact) (V : X.Opens) :
    letI := sectionModule c S.X₃ V
    letI := cohomologyModule X.sheaf c S.X₁ 1 V
    Γ(S.X₃,V) →ₗ[ℂ] (additiveSheaf X.sheaf S.X₁).H'.{1} 1 V := by
  letI := sectionModule c S.X₃ V
  letI := cohomologyModule X.sheaf c S.X₁ 1 V
  let d := (openConnecting hs 0 V).comp
    (sectionsEquiv (additiveSheaf X.sheaf S.X₃) V).symm.toAddMonoidHom
  refine { d with map_smul' := ?_ }
  intro z x
  change openConnecting hs 0 V ((sectionsEquiv (additiveSheaf X.sheaf S.X₃) V).symm
    ((coefficientOn X.sheaf c V z : Γ(X,V)) • x)) = _
  exact (congrArg (openConnecting hs 0 V) (sectionsEquiv_symm_scalar X.sheaf c S.X₃ V z x)).trans
    (openConnecting_naturality hs hs (moduleScalarComplexEnd X.sheaf c S z) 0 V _)

end CycleQ2HodgeConnectingScalar
end

#print axioms CycleQ2HodgeConnectingScalar.sectionBoundary
