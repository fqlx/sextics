# Weighted reduction of the endpoint connection

This is a constructive reduction, not a primitive or certificate. The fixed
endpoint curve is

\[
 Z^2=R(p,H,C)=(H+Cp)^2-4p^6,
 \qquad \omega_j=p^j\,dp/Z,\quad j\in\{0,1,3,4\}.
\]

Use column vectors for connection matrices: the column indexed by `j` is the
cohomology class of the parameter derivative of `omega_j`. For
\(E=6H\partial_H+4C\partial_C\), direct differentiation gives the exact
relative one-form identity

\[
 \nabla_E\omega_j=(2j-4)\omega_j
                  -2\,d_p(p^{j+1}/Z).
\]

Indeed \(ER=12R-2pR_p\), and the product rule proves the displayed formula.
Consequently, if \(M_H,M_C\) are the connection matrices,

\[
6HM_H+4CM_C=\operatorname{diag}(-4,-2,2,4).
\]

This fixes an independent sign and transpose check for the reconstructed
connection, including both second-kind columns.

## One essential parameter after a finite extension

Adjoin \(\lambda\) with \(\lambda^3=H\) and put

\[
t=C/\lambda^2,\quad p=\lambda u,\quad Z=\lambda^3V.
\]

Then

\[
 V^2=(1+tu)^2-4u^6,\qquad
 \omega_j=\lambda^{j-2}\bar\omega_j,
 \qquad \bar\omega_j=u^jdu/V.
\]

Write \(S=\operatorname{diag}(\lambda^{-2},\lambda^{-1},\lambda,\lambda^2)\).
For coefficient columns, \(\sum f_j\omega_j=\sum (Sf)_j\bar\omega_j\).
If \(B(t)\) is the one-parameter connection on the barred basis, then

\[
 M_C=\lambda^{-2}S^{-1}B(t)S,
\qquad
 M_H=\frac1{3H}\left(J-2tS^{-1}B(t)S\right),
 \quad J=\operatorname{diag}(-2,-1,1,2).
\]

Here the matrices act on coefficient columns; these formulas follow by
applying the derivatives to \(Sf\), with \(\partial_Ct=\lambda^{-2}\) and
\(\partial_Ht=-2t/(3H)\). Equivalently,
\(B(t)=\lambda^2SM_CS^{-1}\); every entry on the right must be independent
of \(\lambda\). The discriminant factor becomes
\(4C^6-729H^4=\lambda^{12}(4t^6-729)\).

## The exact physical source direction

On \(X_0=1\), let

\[
H=1+x^6+y^6+z^6+xyz/2,\qquad C=x^3z/2+xy/3.
\]

The recorded source is \(-y^3\nabla_H\omega_0/6\) times
\(dx\wedge dy\wedge dz\). Euler reduction gives

\[
-\frac{y^3}{6}M_He_0
=\frac{y^3}{9H}(e_0+CM_Ce_0).
\]

In the barred basis the same one-form-valued source is

\[
 \frac{y^3}{9H^{5/3}}
 \nabla_t(t\bar\omega_0)
 \wedge dx\wedge dy\wedge dz.
\]

The factor \(y^3/H^{5/3}\) is a physical variable coefficient. It cannot be
treated as constant when integrating in a direction that changes \(t\).
Doing so recreates the missing correction in the physical Jacobian source.
The reduction isolates one cyclic source derivative but does not remove
this coefficient or establish rational exactness.

For a physical current with coefficient columns \(a_x,a_y,a_z\), set
\(b_i=Sa_i\). Its covariant divergence equation transforms to

\[
 \sum_{i=x,y,z}\left(\partial_i b_i+t_iB(t)b_i\right)
 =\frac{y^3}{9H^{5/3}}(I+tB(t))e_0.
\]

This equation retains all four components and all physical derivatives.
It is a useful smaller representation for a constructive current search;
any proposed solution must still be checked in the physical coordinates
and descended from the finite extension.
