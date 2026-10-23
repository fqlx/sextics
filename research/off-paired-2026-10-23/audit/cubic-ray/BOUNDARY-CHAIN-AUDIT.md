# Independent finite normal-chain audit

The relative chain reduction and its parameter-jet formulas are correct.
Their absolute versions require explicit external corrections. The updated
`scaling/boundary-jets/full-log-chain-identity.md` makes that distinction.
This reduces the source to finite representative classes; it does not supply
their primitives or a certificate. No certificate has been found.

Write \(\tau=d_{\rm aux}^3\) for the auxiliary boundary coordinate,
distinct from the physical parameter \(ST\). External coefficient
derivations fix \(u,v,\tau\). Set

\[
\Omega=du\wedge dv,\quad
\alpha=\frac{P_2}{9\tau(G-\tau)^2}\Omega\wedge d\tau,
\quad F=\frac{P_2}{9G(G-\tau)},\quad L=\frac{P_2}{9G^2}.
\]

The sign of \(\alpha\) agrees with the physical boundary normal: the raw
second-normal coefficient for \(J=G-d_{\rm aux}^3-e_{\rm aux}^3\) is
\(-P_2/(3d_{\rm aux}e_{\rm aux}^6)\). Placing \(dJ\) first in the order
\((u,v,d_{\rm aux},e_{\rm aux})\) reverses that sign. Substituting
\(\tau=d_{\rm aux}^3\) then gives exactly the positive displayed form.

Only rational logarithmic differentials are used. In the relative complex
on \((u,v,\tau)\),

\[
h=d_{\rm rel}\log\frac\tau{G-\tau}
=-\frac{d_YG}{G-\tau}+\frac{G\,d\tau}{\tau(G-\tau)}.
\]

Both terms matter: \(d_{\rm rel}h=0\), and dropping the \(d_YG\) term
breaks the homotopy after multiplication by a plane one-form. For example,
with \(\rho=du\), the omitted term is what cancels the nonzero
\(\partial_v[G/(\tau(G-\tau))]\) contribution.

The exact identities are

\[
\alpha=d_{\rm rel}(F\Omega)+L\Omega\wedge h,
\]
\[
L\Omega=\sigma+d_Y\rho
\quad\Longrightarrow\quad
\alpha=\sigma\wedge h+
d_{\rm rel}(F\Omega+\rho\wedge h).
\]

Here \(\rho\) is a plane one-form independent of the auxiliary \(\tau\).
The sign before \(\rho\wedge h\) is positive; the negative signs in the
Griffiths plane reduction are already included in the definition of
\(\rho\).

## Parameter jets

For every commuting external coefficient derivation \(D\), put

\[
\ell_D=-\frac{DG}{G-\tau},\qquad
H_D=DF+L\ell_D
=\frac{(DP_2)G(G-\tau)-P_2(DG)(3G-2\tau)}
       {9G^2(G-\tau)^2}.
\]

Direct differentiation checks every component of
\(D h=d_{\rm rel}\ell_D\), including its \(du,dv\) components, and gives

\[
D\alpha=(DL)\Omega\wedge h+d_{\rm rel}(H_D\Omega).
\]

Thus reducing \((DL)\Omega=\sigma_D+d_Y\rho_D\) gives

\[
D\alpha=\sigma_D\wedge h+
d_{\rm rel}(H_D\Omega+\rho_D\wedge h).
\]

This is an explicit rational chain correction. It assumes no unknown
scalar primitive or derivative of such a primitive. The finite inverse
operators and all their coefficient derivatives remain part of its actual
rational data.

## Absolute corrections cannot be silently omitted

If \(z\) denotes the external coordinates, let \(d=d_{\rm rel}+d_z\).
The absolute identity corresponding to the first relative identity is

\[
d(F\Omega)+L\Omega\wedge d\ell
=\widehat\alpha,
\qquad
\widehat\alpha=\alpha+\sum_D H_D\,dz_D\wedge\Omega.
\]

The extra terms are generally nonzero: at \(G=2,P_2=1,\tau=1,DG=1,DP_2=0\),
the coefficient is \(-1/9\). After the plane reduction, the absolute
identity is

\[
\widehat\alpha=\sigma\wedge d\ell+
d(F\Omega+\rho\wedge d\ell)-d_z\rho\wedge d\ell.
\]

This explains exactly which terms would be lost by simply replacing
\(d_{\rm rel}\) with \(d\). The constructive note now restricts its boxed
identities to the relative complex and records these external corrections.

At the particular stage where the source is wedged with an external top
three-form \(\Theta\), with coefficients depending only on that base,
\(d\Theta=0\) and all external-degree-one corrections wedge to zero.
The primitive transports with the sign

\[
\Theta\wedge d_{\rm rel}\eta=-d(\Theta\wedge\eta).
\]

After a contraction lowers the external degree, that vanishing no longer
holds automatically; the displayed parameter corrections must then be used.

## Exact finite plane module

The independent audit reconstructs all 191 columns of the degree-nine and
degree-fifteen operators \(M_m\) from their Fermat division rule. All exact
Jacobian identities pass. At degree nine there are 55 monomials and ten
standard monomials; at degree fifteen there are 136 monomials and no standard
ones. Together with the ten degree-three pole-one monomials, these give the
twenty retained plane representatives.

Every operator is the identity at \(\lambda=0\). More specifically, it is
the identity at \(B=0\) for every \(\lambda\), and the actual physical family
contains that Fermat locus with \(ST\ne0\). Its determinant therefore also
does not vanish identically after physical pullback. The inverse and its
coefficient derivatives are defined rationally at the generic physical
point; no generic-rank assumption is needed.

The plane reduction lifts to the boundary with the explicit Euler defect
\(E_Y(J)-6J=6(d_{\rm aux}^3+e_{\rm aux}^3)\). Its double logarithmic
boundary residue is zero. Differentiating physical parameters or taking a
normal derivative in a \(Y\) direction does not turn either positive cubic
boundary power into the missing double-log coefficient.

`verify_boundary_chain_fraction.py` passed twenty audit groups, including
all 191 exact operator columns, the physical normal source, relative and
parameter-jet identities, nonzero absolute corrections and boundary defect.
It imports no primary construction code and uses standard-library Fraction
polynomial/rational arithmetic. The remaining twenty representative classes
have not been supplied with source-compatible scalar primitives.
