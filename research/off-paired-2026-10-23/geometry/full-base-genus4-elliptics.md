# The full coefficient-retaining base curve and its elliptic quotients

This is an exact auxiliary decomposition, not a primitive or certificate.

Put

\[
 s=-3z/2,\quad L=H+sC,\quad b=3z^2/4,\quad B=L-1-z^6.
\]

Then the actual base curve at fixed \(L,z\) satisfies

\[
 y^6=-x^6+bx^3+B.
\]

The diagonal order-three action \((x,y)\mapsto(\zeta x,\zeta^{-1}y)\)
preserves both the source differential \(dx/y^2\) and the actual coefficient
\(C=x^3z/2+xy/3\). Its quotient uses

\[
 t=x^3,\quad u=xy,\quad
 u^6=t^2Q(t),\quad Q(t)=-t^2+bt+B,
\]

and retains

\[
 C=tz/2+u/3,\qquad \frac{dx}{6y^2}=\frac{dt}{18u^2}.
\]

This is a genus-four curve on the generic smooth open. The involution
\(\rho:u\mapsto-u\) loses \(C\); its genus-two quotient alone cannot carry
an arbitrary endpoint kernel depending on \(C\).

## Two additional, isotrivial elliptic factors

Adjoin \(\kappa\) with \(\kappa^2=-B\). The involution

\[
 \sigma:(t,u)\longmapsto(\kappa^2/t,\kappa u/t)
\]

preserves the genus-four curve and commutes with \(\rho\). Set

\[
 w=u^2/t,\quad Y_\pm=u(1\pm\kappa/t).
\]

The elliptic quotients by \(\sigma\) and \(\sigma\rho\) are

\[
 Y_\pm^2=w(b\pm2\kappa-w^3).
\]

Equivalently, with \(X=1/w\) and \(W_\pm=Y_\pm/w^2\),

\[
 E^0_\pm:\quad W_\pm^2=(b\pm2\kappa)X^3-1.
\]

These have \(j=0\), hence become the fixed Fermat elliptic curve after a
finite coefficient extension and rescaling. Their differential pullbacks are

\[
 \frac{dX}{W_+}=\frac{t(t-\kappa)}{3u^5}dt,\qquad
 \frac{dX}{W_-}=\frac{t(t+\kappa)}{3u^5}dt.
\]

The quotient by \(\rho\) has

\[
 R=t+B/t,\qquad R^2=(w^3-b)^2+4B,
\]

\[
 \frac{dw}{R}=-\frac{t}{3u^4}dt,\qquad
 w\frac{dw}{R}=-\frac{dt}{3u^2}.
\]

It is the genus-two curve that splits into the two varying elliptic curves
in the companion-density calculation. The standard commuting-involution
Jacobian decomposition therefore has dimensions \(1+1+2=4\), with two
isotrivial elliptics and this genus-two factor.

## What is and is not carried by this decomposition

The actual density \(dt/(18u^2)\) is \(\rho\)-invariant and
\(\sigma\)-anti-invariant; by itself it belongs to the genus-two quotient
part, not to the two isotrivial elliptic factors. A kernel containing
\(C=tz/2+u/3\) need not be \(\rho\)-invariant. Its odd and even parts must
both be retained, together with all coefficient variations and finite-trace
corrections. The displayed elliptic decomposition does not authorize
replacing the entire source-carrying kernel by an elliptic differential.

The isotrivial factors provide a concrete place where the maintained Fermat
elliptic machinery could enter a future construction, after actual scalar
primitives and derivative compatibility have been established.

Prepared with OpenAI Codex assistance.
