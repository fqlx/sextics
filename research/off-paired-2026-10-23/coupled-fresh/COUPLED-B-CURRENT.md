# An explicit partial current in the complete two-component gauge

This is a source-carrying identity, not a primitive or certificate. It retains
both components, including their physical divergences. It is useful as an
actual residual equation for a prospective correction using all four base
directions.

Use the birational chart `(z,U,B,C)` from
[the coefficient-chart calculation](relative/B-LINEAR-SOURCE.md). Put

\[
 L=2+3zU,\quad Q=C-z^{-2}-U^6,\quad
 K=\frac{6B-3U}{L},\quad H=1+z^2+\frac{K^6}{Q}.
\]

The physical volume is

\[
 \Omega=-\frac{dz\wedge dU\wedge dB\wedge dC}{3z^2LQ}.
\]

It has no B-dependent density, and

\[
 H_B=\frac{36K^5}{LQ},\qquad
 \partial_B\log\kappa=\frac3B-\frac{2H_B}{H},\qquad
 \kappa=\frac{B^3}{CH^2}.
\]

On the cubic `Cp^3+Bp+H=0`, write `g=B+3Cp^2`, and retain the canonical
`V=-H/(pg)-1/3`, `W=CH Bp/g^3`. The universal coefficient derivative
`q=p_B=-p/g` satisfies the particularly simple identities

\[
 q=-\frac{9H}{2B^2}V-\frac{H(4\kappa+27)}{B^2}W,
 \qquad
 q_H=\frac{3}{2B^2}(V+6W).
\]

Here the subscripts on `p_B` and `q_H` are universal coefficient derivatives,
with the other two cubic coefficients held fixed. They must be distinguished
from physical chart derivatives.

Consequently the actual rational currents

\[
 A_0=-\frac{9H}{4B^2}\partial_B,\qquad
 D_0=-\frac{H(4\kappa+27)}{2B^2}\partial_B
\]

satisfy the two exact coupled equations with explicit residuals:

\[
 \operatorname{div}_\Omega A_0+
 \frac3{4\kappa+27}D_0(\log\kappa)
 =\frac{3H_B}{4B^2},
\]

\[
 \operatorname{div}_\Omega D_0-2A_0(\log\kappa)+
 \frac{27-2\kappa}{4\kappa+27}D_0(\log\kappa)
 =\frac1{HC}+\frac{9H_B}{2B^2}.
\]

Thus the missing full correction `(A_1,D_1)` would have the right-hand side

\[
 -\frac{3H_B}{4B^2}(1,6).
\]

The remaining direction `(1,6)` is independent of kappa. No correction for it
has been obtained. The chart keeps `z,U` fixed exactly when it keeps the
original ratios `X1/X0,Y1/Y0` fixed; therefore solving only within the B,C
surface would re-enter the existing original-ratio obstruction. Any proposed
completion must include the horizontal z or U directions.

The current is the physical identity

\[
 \operatorname{div}_\Omega\left(\frac q2\partial_B\right)
 =R+\frac{H_B}2q_H.
\]

Its first component has nonzero divergence in general; no pure-component or
closed-time conclusion is being used. `verify_coupled_B_current.py` checks the
two cubic identities and both coupled equations exactly (five checks), in
addition to the child calculation's nine exact coordinate/source checks.

Prepared with OpenAI Codex assistance.
