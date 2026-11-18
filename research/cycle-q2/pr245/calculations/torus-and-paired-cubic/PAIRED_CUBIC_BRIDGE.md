# Exact bridge to the paired-ratio cubic

Use α=Y₀/X₀, β=Y₁/X₁ and γ=Y₂/X₂ as passive coordinates, and (U:V:W)=(X₀²:X₁²:X₂²) as active plane coordinates. The cubic already recorded in [Discussion 61, paired-ratio cubic](https://github.com/hodge-computer/sextics/discussions/61#discussioncomment-19135828) is

    F_pair=(1+α⁶)U³+(1+β⁶)V³+(1+γ⁶)W³
           +(αβU²V+βγV²W+αγUW²)/2.

Put v=V/U and w=W/U. In the recent fibration of the residual set u=I/b². The change of coordinates is

    T=α³,     y=γ,     u=β/α²,     b=v,     p=w/α.

Consequently its cubic H(p,b) equals α⁻³ F_pair(1,v,w) identically. Thus it agrees with the earlier family after a degree-three base change. The deck transformation there sends (α,β) to (ζα,ζ²β). It keeps the target character, including its volume factor, invariant on this subgroup. This is compatible with the nontrivial sector under a different deck action in the elliptic-surface model.

The two normalized numerator presentations also differ by an explicit exterior derivative. Let vol=dα∧dβ∧dγ∧dv∧dw. Directly

    du∧dp∧dT∧dy∧db=(3/α)vol,
    [u²pb/6+2upb³/T] du∧dp∧dT∧dy∧db/H³
      = N vol/F_pair(1,v,w)³,
    N=(α³β²/2)vw+6α²βv³w.

Set Q=α²βw(2v∂v−β∂β), and denote F_pair(1,v,w) by C. The ordinary divergence of Q in vol is zero. The exact polynomial identity

    N=Q(C)−(3/2)α²β²γ v²w²

therefore gives

    N vol/C³ = −(3/2) α²β²γ v²w² vol/C³ − (1/2)d(C⁻² ι_Q vol).

This formula transports partial currents with their horizontal derivatives included. It explains how the previous cubic six-degree protected source appears with the indicated normalization.

The earlier calculation already identifies the residual as a second variation over the base. Fibrewise pole reduction of the sextic-on-cubic numerator alone loses these base derivatives. The earlier Weierstrass reduction also retains a nontrivial triple-cover target character, and the pulled-back elliptic surface has χ=3, p_g=2. The rational-elliptic-surface primitive theorem from the pole-one example does not directly apply. [Discussion 61, cycle-three Jacobian route](https://github.com/hodge-computer/sextics/discussions/61#discussioncomment-19148488)

The later Noether–Lefschetz calculation describes ordinary algebraic specializations and explicitly leaves an off-diagonal Gysin/Leray term unresolved. Its finite-field rank observations do not supply a global correction. [Discussion 61, Noether–Lefschetz data and stated gap](https://github.com/hodge-computer/sextics/discussions/61#discussioncomment-19503129)

The standard-library torus_griffiths.py additionally verifies the cubic after the full monomial substitution, its signed Jacobian, both numerator terms, the vector-field divergence and the polynomial current identity over ℚ.
