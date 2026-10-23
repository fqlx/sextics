# Quartic and canonical models for the constant-source quotient

No primitive or certificate is supplied. On \(X_0=1\), write
\(x=X_1,y=Y_0,z=Y_1,a=X_2,b=Y_2\), and set

\[
u=xy,\qquad v=y^3.
\]

The Jacobian is \(\partial(u,v)/\partial(x,y)=3v\), so the exact target
density becomes constant:

\[
y^3\,dx\wedge dy=du\wedge dv/3.
\]

With

\[
D=1+z^6+a^6+b^6,\quad B=zab/2,\quad L=z/2+ab/3,
\]

the equation is

\[
F=u^6/v^2+v^2+D+B u^3/v+Lu,
\qquad G=v^2F=u^6+v^4+(D+Lu)v^2+B u^3v.
\]

The physical pole-two density is therefore \(v^4/(3G^2)\), retaining all
three passive-coordinate differentials. The Newton polygon of a generic
fixed-\((D,B,L)\) curve has vertices \((6,0),(0,4),(0,2)\), area six and
boundary lattice length six, hence four interior points. This is a genus-four
curve, so treating the quartic in \(v\) as an elliptic curve would omit
geometry.

## Canonical complete intersection and trigonal rulings

The projective quotient has canonical coordinates

\[
r=x^3,\quad s=y^3,\quad h=X_0^3,\quad w=xyX_0,
\]

and is the intersection

\[
w^3=rsh,\qquad Q=r^2+s^2+Dh^2+Brh+Lwh=0.
\]

The cubic is a rational toric cubic surface. The quadric is generically
smooth when \(L\ne0\), so its two rulings give the two trigonal pencils of
the genus-four curve.

For an explicit ruling, fix \(i^2=-1\), put
\(K=D-B^2/4\), \(A=r+Bh/2+is\), \(E=r+Bh/2-is\). Then

\[
Q=AE+h(Kh+Lw).
\]

In the chart \(h=1\), set \(A=t,E=e\). The quadric is parametrized by

\[
r=(t+e-B)/2,\quad s=(t-e)/(2i),\quad w=-(te+K)/L.
\]

The curve equation is the bidegree-\((3,3)\) relation

\[
4i(te+K)^3+L^3(t+e-B)(t-e)=0.
\]

This gives explicit cubic resolvents but no elliptic factor or primitive
automatically.

## A K3 model and its essential physical coefficient

Fix the nonlinear parameters \(z\) and \(c=ab\). Put

\[
W=a^3-b^3,\qquad S=a^3+b^3,
\qquad S^2=W^2+4c^3.
\]

Then \(F=0\) implies the sextic double-plane equation

\[
W^2=-\left[x^6+y^6+\frac{zc}{2}x^3+
\left(\frac z2+\frac c3\right)xy+1+z^6+2c^3\right].
\]

When the branch sextic is smooth this is a K3 surface. It has the symplectic
order-three action \((x,y)\mapsto(\zeta x,\zeta^{-1}y)\). Its quotient is
birational to the double cover of the toric cubic branched in the quadric
above, making a Kummer or Shioda--Inose correspondence a concrete question.

However,

\[
da\wedge db=-\frac{dc\wedge dW}{3S}.
\]

The physical source keeps the factor \(1/S\). The deck transformation
\((a,b)\mapsto(-b,-a)\) fixes \(c,W,F\), negates \(S\), and negates the
physical volume. Consequently forgetting \(S\) to the K3 model discards the
required anti-invariant source. Any useful K3 correspondence must retain
this cover coefficient and prove the exact source transport.
