# Global rational current removing the full second-kind source projection

Let E=H¹(C), N=H¹(D), e=e_τ, and w=−[η]/(4I). The current target
is e⊗w, with curl convention ∇_I U−∇_J V. Keep the independent
genus-ten frame of ten holomorphic φ, nine ψᵢ=∇_Jφᵢ, and σ. Write
ψ=ψ₀=∇_Jφ₇₁. Define the rational moduli functions

    m=⟨w,K⟩,    n=⟨ψ,∇_J K⟩=(10/3)⟨ψ,φ₇₂⟩,    q=m/n.

The explicit formulas in the paired-curve packets compute the two
pairings by finite traces; neither uses an unspecified primitive.
At (I,J)=(3,7), n is a nonzero rational number. The global
HOLOMORPHIC_KERNEL.md identities give ⟨ψ,K⟩=0, hence
⟨∇_Jψ,K⟩=−n. Thus w+q∇_Jψ has zero σ coefficient everywhere as a
rational class. Determine its remaining 19 rational coefficients from
the already constructed connection and pairing frame:

    w+q∇_Jψ = H + Σ_{i selected} t_i ψ_i,
    H = Σ_{k=0..9} h_k φ_k.

Every h,t coefficient is an explicit rational function of (I,J)
given by the degree-21/24 finite-trace recipes. No differential
equation needs to be solved to obtain these coefficients. Set

    U=0,
    V=qe⊗ψ − Σ_i (t_i e)⊗φ_i − ∇_J^C(qe)⊗φ₀,

where φ₀=φ₇₁. By the covariant product rule and ∇_Jφ_i=ψ_i,

    e⊗w + ∇_J V
      = e⊗H − Σ_i ∇_J^C(t_i e)⊗φ_i − (∇_J^C)²(qe)⊗φ₀.

This is an exact global proper-current reduction of the actual physical
source. The residual is in E⊗H⁰(Ω_D), pointwise rank 80, and has zero
component in E⊗H¹(𝒪_D). That Hodge subspace need not be preserved by the
connections. The formula is not a smaller flat rank-80 connection, and
it does not yet prove the displayed residual vanishes. The standard
lifting by rational forms gives a literal partial three-form, with a
relative-exact correction obtainable by the finite quartic primitive test.

At the rational fibre (3,7), q equals

    −9471832684659617628261442742257292547 /
     19398433382880087487005428605975533980.

Its reduction modulo 43 is 1. At that reduction, h and t are

    h=(19,29,39,12,1,28,27,41,36,29),
    t=(19,29,15,1,35,34,7,42,10).

The sibling global_hodge_current.py uses the independently verified
Gram matrix, source coordinates and full connection to compute these
values and all exact rational h,t values. Its zero σ test passes
over Q and F43.
