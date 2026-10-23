# A coefficient-retaining quotient with constant physical source

This is an exact coordinate interface, not a rational current or certificate.

On the fixed chart, let \(x=X_1,y=Y_0,z=Y_1,a=X_2,b=Y_2\), and

\[
 F=a^6+b^6+C ab+H,\quad
 H=1+x^6+y^6+z^6+xyz/2,\quad C=x^3z/2+xy/3.
\]

The order-three action \((x,y)\mapsto(\zeta x,\zeta^{-1}y)\)
preserves \(H,C\) and the actual density \(y^3dx\wedge dy\).
Use rational quotient coordinates

\[
 u=xy,\qquad v=y^3.
\]

Then the physical source becomes constant:

\[
 du\wedge dv=3y^3dx\wedge dy.
\]

Both coefficients are retained explicitly:

\[
 H=1+u^6/v^2+v^2+z^6+uz/2,\quad
 C=u^3z/(2v)+u/3.
\]

Clearing the base pole by \(G=v^2F\) gives

\[
 G=u^6+v^4+
 (1+z^6+a^6+b^6+uz/2+uab/3)v^2
 +(u^3zab/2)v.
\]

Consequently the original five-form is exactly

\[
 \frac{y^3\,dx\,dy\,dz\,da\,db}{F^2}
 =\frac{v^4\,du\,dv\,dz\,da\,db}{3G^2}.
\]

This quotient retains the coefficient \(C\), unlike passing from \(y\)
to \(y^2\) alone. It can be used for a source-carrying rational-current
construction with Laurent coefficients in \(v\). The displayed polynomial
source does not automatically imply polynomial-family integration, and the
clearing factor \(v^2\) must remain in source transport.

## Potential-basis construction gap

For the rank-five basis \(\omega_j=p^jdp/Z\), the rational potentials
\(\nu_j=-p^{j+1}d\log r/(j+1)\) satisfy

\[
 d\nu_j=dH\wedge\omega_j+dC\wedge\omega_{j+1}.
\]

A divergence-free current in this basis avoids differentiating its
coefficients, but still needs the actual directional equation
\(\sum_j(T_j(H)\omega_j+T_j(C)\omega_{j+1})\) equal to the original
source. Taking every \(T_j\) tangent to \(H\) or \(C\) reduces this to
rational integration on the fixed coefficient curve; it does not remove the
coefficient-kernel variation. No fields satisfying the full equation have
been constructed here.

## Full coefficient map for the split-quadric presentation

Let

\[
 e=zab/2,\quad f=z/2+ab/3,\quad g=1+z^6+a^6+b^6.
\]

With \(w=x^3=u^3/v\), one has

\[
 F=v^2+w^2+ew+fu+g,\qquad u^3=wv.
\]

This retains every term and the actual source above. If
\(p=ab\), \(Z=b^6-a^6\), the actual coefficient Jacobian is

\[
 \frac{d(e,f,g)}{d(z,a,b)}=\frac{(2p-3z)Z}{2}.
\]

Consequently the full physical five-form has coefficient
\(2/[3(2p-3z)Z]\) in \((u,v,e,f,g)\). The coefficient is not constant even
though the universal equation is linear in \(g\). Setting
\(d^2=f^2-4e/3\), the inverse branches satisfy

\[
 z=f\pm d,\quad p=\frac32(f\mp d),\quad
 Z^2=(g-1-z^6)^2-4p^6.
\]

Thus universal integration would still have to retain the explicit
\(1/(dZ)\) coefficient and its derivatives. No cancellation of that
correction has been obtained here.
