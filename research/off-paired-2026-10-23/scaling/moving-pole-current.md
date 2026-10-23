# A sufficient rational current with a moving endpoint pole

No solution to the criterion below has been found. It is a constructive
enlargement using a denominator in the endpoint coordinate.

Work on \(X_0=1\), with base coordinates \(x,y,z\),

\[
H=1+x^6+y^6+z^6+xyz/2,\quad C=x^3z/2+xy/3,
\quad Z^2=R(p)=(H+Cp)^2-4p^6.
\]

The physical source is
\(-y^3\nabla_H\omega_0/6\) times \(dx\wedge dy\wedge dz\), where
\(\omega_0=dp/Z\). Extend base derivations with \(p\) fixed.

Suppose rational base functions \(s\) and a rational vector field
\(V=(V_x,V_y,V_z)\) satisfy

\[
\operatorname{div}V=0,\qquad V(s)=0,\qquad
V(H)+sV(C)=0,\qquad V(C)=-y^3/6.
\]

Then the rational one-form-valued current

\[
\alpha_i=\frac{V_i}{p-s}\omega_0
\]

has exactly the required covariant divergence. In fact, direct product-rule
calculation, before any cohomology reduction, gives

\[
\sum_i\nabla_i\alpha_i
=\left(\frac{\operatorname{div}V}{p-s}
       +\frac{V(s)}{(p-s)^2}\right)\omega_0
 +\frac{V(H)+pV(C)}{p-s}\nabla_H\omega_0
=-\frac{y^3}{6}\nabla_H\omega_0.
\]

There is no finite-extension issue in this expression. Its new endpoint
denominator \(p-s\) is what distinguishes it from coefficient-only compact
currents. Transport, denominator legality and homogeneous clearing would
still need explicit verification after a solution \(s,V\) is supplied.

Equivalently, one can seek a divergence-free \(V\) with the prescribed
\(V(C)\), define \(s=-V(H)/V(C)\), and impose \(V(s)=0\). Along its
integral curves the slope \(dH/dC=-s\) is constant.

## Interpretation through a moving third-kind differential

Adjoin \(w\) with \(w^2=R(s)\), and set

\[
\Omega_s=\frac{w}{p-s}\frac{dp}{Z}.
\]

This has constant residues \(+1,-1\) at the two points above \(p=s\).
For an arbitrary base derivation \(\partial_v\), with \(s_v=\partial_vs\)
and
\(w_v=[R_v(s)+s_vR_p(s)]/(2w)\), one has

\[
\partial_v\Omega_s
-d_p\left(\frac{-ws_v}{(p-s)Z}\right)
=T_v(p)\frac{dp}{Z^3},
\]

where

\[
T_v(p)=\frac{w_vR(p)-\frac w2(R_v(p)+s_vR_p(p))}{p-s}.
\]

The numerator vanishes at \(p=s\), so \(T_v\) is a polynomial of degree at
most five. Existing Dwork reduction handles its compact connection column.
For the sufficient current above, \(M=V/w\) has \(M(w)=0\) and zero
divergence, and \(M_i\Omega_s=\alpha_i\); the quadratic extension cancels.

The concrete nonlinear section \(s=q=xy\) is coupled to the physical source,
and at the seed of `nonlinear-cz-seed.md` it has
\(w=a^2-q^6/a^2\). No vector field meeting the four conditions is supplied.
