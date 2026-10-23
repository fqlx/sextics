# Full rational dlog chain identity and its exact scope

No class primitive is constructed. This records a source-carrying finite
relative chain reduction, its parameter derivatives, and the distinction
from an absolute primitive.

Let the external coefficient field contain the first Fano coordinates
`X,S,T`, and let the relative coordinates be `(u,v,tau)`, with
`tau=d_aux³`. External derivations fix these three relative coordinates.
Let `G(u,v)` be the complete moving ternary sextic in the affine chart
`Y0=1`, and let `P2(u,v)` be the actual numerator. Put

\[
 L=\frac{P_2}{9G^2},\qquad F=\frac{P_2}{9G(G-\tau)},
 \qquad \ell=\log\frac\tau{G-\tau}.
\]

Only the rational differential `d_rel ell` is used; no logarithm is
adjoined as a function. The normal calculation in
`../cm-companion/log-boundary-normal-homotopy.py` gives the ordered
relative three-form

\[
 \alpha=\frac{P_2}{9\tau(G-\tau)^2}
 du\wedge dv\wedge d\tau.
\]

Write `Omega=du wedge dv`. The FULL closed rational differential is

\[
 d_{\rm rel}\ell=
 -\frac{G_u\,du+G_v\,dv}{G-\tau}
 +\frac{G\,d\tau}{\tau(G-\tau)}.
\]

As `Omega` already has top `Y` degree,

\[
 \boxed{\alpha=d_{\rm rel}(F\Omega)+L\Omega\wedge d_{\rm rel}\ell.}
\]

Suppose the exact plane reduction gives

\[
 L\Omega=\sum_j s_j\omega_j+d_Y\rho,
\]

where the twenty `omega_j` are the rational two-form representatives
from `actual-source-finite-jets.md`, and `rho` is a rational ONE-form in
`du,dv`, independent of the auxiliary `tau`. Then

\[
 \boxed{\alpha=\sum_j s_j\omega_j\wedge d_{\rm rel}\ell
 +d_{\rm rel}\left(F\Omega+\rho\wedge d_{\rm rel}\ell\right).}
\]

The mixed `du,dv` components of `d_rel ell` are essential in the
correction `rho wedge d_rel ell`. Keeping only its `d tau` component
would leave a nonzero mixed derivative error.

## Every external parameter derivative

For an external derivation `D`,

\[
 D(d_{\rm rel}\ell)=d_{\rm rel}(D\ell),\qquad
 D\ell=-\frac{DG}{G-\tau}.
\]

Because `L Omega` is relatively closed, one obtains the exact identity

\[
 \boxed{D\alpha=(DL)\Omega\wedge d_{\rm rel}\ell
 +d_{\rm rel}\left[(DF+L\,D\ell)\Omega\right].}
\]

Reduce `(DL)Omega` using the same proved rational operators. If
`(DL)Omega=sum a_j omega_j+dY rho_D`, then the full source jet is

\[
 D\alpha=\sum_j a_j\omega_j\wedge d_{\rm rel}\ell
 +d_{\rm rel}\left[(DF+L D\ell)\Omega
 +\rho_D\wedge d_{\rm rel}\ell\right].
\]

All `DG`, `DP2`, `D lambda`, `D B` and inverse-matrix derivatives occur
in explicit rational functions. The first elliptic derivatives can be
combined with the checked two-function `(qE,N)` system in
`../../jacobian/CARDANO-FIRST-ELLIPTIC-MODULE.md`. This gives a finite
source/jet module with at most forty representatives. Its representative
classes have not been served by scalar primitives.

## Relative versus absolute differential

The displayed boxes use `d_rel` only. If the external parameters also
vary, the absolute differential adds external-degree-one terms. More
explicitly, with external coordinates `z_D` placed first, define

\[
 H_D=DF-\frac{L DG}{G-\tau},\qquad
 \widehat\alpha=\alpha+\sum_D H_D\,dz_D\wedge\Omega.
\]

Then `alphahat=d_abs(F Omega)+L Omega wedge d_abs ell`. Writing
`sigma=sum s_j omega_j`, the complete absolute identity is

\[
 \widehat\alpha=\sigma\wedge d_{\rm abs}\ell
 +d_{\rm abs}(F\Omega+\rho\wedge d_{\rm abs}\ell)
 -d_{\rm ext}\rho\wedge d_{\rm abs}\ell.
\]

Both the explicit `H_D` terms and the last mixed term are mandatory. In
the form where the representative term still uses `d_rel ell`, writing
the second boxed identity as `alpha=representatives+d_rel eta` gives

\[
 \alpha=\text{representatives}+d_{\rm abs}\eta-d_{\rm ext}\eta.
\]

The parameter identities above explicitly describe those external
corrections; they are not presumed zero. Likewise substituting full
`d_abs ell` in the representative term introduces its known external
components, which must be subtracted.

At the particular top-form reduction stage, the source is multiplied by
the external top three-form `Theta` on `W_H`, with a coefficient depending
only on that base. Then `d_ext Theta=0` and
`Theta wedge d_ext eta=0`, so the relative homotopy transports to the
absolute source with
`Theta wedge d_rel eta = -d_abs(Theta wedge eta)`. After further
contractions reduce external degree, the external corrections survive
and must use the displayed jet formulas.

Thus this is an actual finite normal-chain reduction of the physical
boundary source. It is not a proof that its twenty (or forty) remaining
classes vanish, nor a joint primitive for the original fourfold.

Prepared with OpenAI Codex assistance.
