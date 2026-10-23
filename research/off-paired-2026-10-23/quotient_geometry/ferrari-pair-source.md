# An exact source-carrying Ferrari pair correspondence

This note gives a finite correspondence that reconstructs the original
source using constant coefficients. It does not supply a primitive.

Use the quartic and its normalized residue source from
`quartic-normalization.md`:

\[
 G=v^4+Sv^2+Tv+R,\quad R=u^6,\quad T=eu^3,
 \qquad \omega=\operatorname{Res}\frac{v^4\,dv}{3G^2}.
\]

Factor over a finite extension as

\[
 G=(v^2+qv+r)(v^2-qv+s),\quad
 r+s=S+q^2,\quad q(s-r)=T,\quad rs=R.
\]

Let \(P(m)=m^3+2Sm^2+(S^2-4R)m-T^2\), so \(P(q^2)=0\), and
\(D=P'(q^2)\). The unweighted trace over the first quadratic factor is

\[
 \operatorname{Tr}_{\rm pair}\omega
 =\frac{2q[-S(S+q^2)^3+2R(S+q^2)^2+8R^2]}{3D^3}.
\]

Equivalently, if \(S,R,T\) are independent coefficient parameters,

\[
 \boxed{\operatorname{Tr}_{\rm pair}\omega
 =-\frac13\partial_S^2q,\qquad
 \partial_Sq=-\frac{q(S+q^2)}D.}
\]

The derivative is a coefficient derivative holding \(R,T\) fixed. It is
not automatically a physical base derivative with zero divergence.

All displayed residue coefficients use the relative convention in which
\(dv\) is the one-variable differential. For the ambient ordering
\(du\wedge dv\wedge dz\wedge da\wedge db\), placing \(dG\) first
introduces a minus sign: the physical four-form is
\(-\operatorname{Tr}_{\rm pair}\omega\,du\wedge dz\wedge da\wedge db\).
The same overall minus applies to the final quotient four-form below.
The constant reconstruction and constructive exactness obligation are
unchanged by this convention.

## Exact reconstruction of the entire quartic source

Let \(\omega_i\) be the residue at the four simple quartic roots. Their
sum is zero: the rational differential \(v^4dv/(3G^2)\) has no residue at
infinity. For a fixed original root \(i\), let \(j,k,l\) be the others.
Then

\[
 \boxed{\omega_i=\frac12[(\omega_i+\omega_j)
                          +(\omega_i+\omega_k)
                          +(\omega_i+\omega_l)].}
\]

Each parenthesized term is a Ferrari pair trace, taken through one of the
three derivative-compatible embeddings of the ordered-pair field into a
common splitting field. The coefficients \(1/2\) are constant. Therefore
an actual primitive for the full pair source, with its physical density,
would give a primitive for the original source by this constant linear
combination and finite descent. There are no varying trace-dual weights in
this reconstruction. A primitive for only one trace does not suffice.

## Conic parameter and physical density

In the actual coefficient field, write

\[
 S=g+fu,\quad e=zab/2,\quad f=z/2+ab/3,\quad
 g=1+z^6+a^6+b^6.
\]

The pair field contains

\[
 k=q(S+q^2)/u^3,\qquad k^2=4q^2+e^2.
\]

Thus it is birational to the conic parameter model

\[
 q=e(\tau-\tau^{-1})/4,\quad k=e(\tau+\tau^{-1})/2,
 \quad u^3=(q/k)(g+fu+q^2).
\]

At fixed \((z,a,b)\), put \(d=\tau-\tau^{-1}\),
\(\rho=\tau+\tau^{-1}\), \(h=q/k=d/(2\rho)\). Its actual tangent is

\[
 u_\tau=\frac{hP'(q^2)}{2\tau u^3(3u^2-hf)}.
\]

The pair-source four-form is the displayed pair trace times
\(u_\tau d\tau\wedge dz\wedge da\wedge db\). The denominator
\(3u^2-hf\) and the derivative of the coefficients cannot be dropped.
A primitive depending only on \(\tau\), with \((a,z,b)\) fixed, would
fall in the already-excluded fixed-coordinate-ratio scope. At least one
of those coefficient directions must participate in a successful current.

## Quotient by the physical global Y sign

The physical involution sends
\((u,v,z,b,q)\mapsto(-u,-v,-z,-b,-q)\), with \(e,S,k,a\) fixed.
It sends \(\tau\mapsto\tau^{-1}\). The pair-source four-form is invariant.
Set

\[
 D_\rho=\rho^2-4,\quad U=u/d,\quad Z=z/d,\quad B=b/d,
 \qquad e=D_\rho ZaB/2,
\]

and \(\bar f=Z/2+aB/3\). The quotient pair model satisfies

\[
 2\rho D_\rho U^3-D_\rho\bar fU-1-a^6
 -D_\rho^3\left(Z^6+B^6+\frac{Z^2a^2B^2}{64}\right)=0.
\]

Define the rational covariant differentials

\[
 \mathcal D X=dX+\frac{\rho X}{D_\rho}d\rho
 \quad(X=U,Z,B).
\]

The **entire pair source**, including the coordinate Jacobian, is

\[
 \boxed{\frac{16e[e^2\rho^3+64(4-3\rho^2)U^3]}
 {3(e^2\rho+64U^3)^3}
 \mathcal DU\wedge\mathcal DZ\wedge da\wedge\mathcal DB.}
\]

The cancellation behind this formula is exact: the residue coefficient
scales by \(d^{-3}\), while \(du\wedge dz\wedge da\wedge db\)
scales by \(d^3\). Generic projective fibers over \(\rho\) are weighted
degree-six Calabi–Yau threefolds. They are not automatically serving Fano
fibers. Constructing a rational primitive for this displayed four-form is
the concrete remaining obligation. Once found, the constant pair
reconstruction above recovers the original physical source.

Prepared with OpenAI Codex assistance.
