# Exact transfer from the source-density quotient

This is a conditional witness construction. It does not establish that the
quotient current exists. The variable order in the physical affine formulas is
\((x,y,z,a,b)=(X_1,Y_0,Y_1,X_2,Y_2)\), on \(X_0=1\).
The actual affine projective order \((X_1,X_2,Y_0,Y_1,Y_2)\) differs by two
swaps, so the orientation is unchanged.

Put

\[
\theta(x,y,z,a,b)=(u,v,z,a,b)=(xy,y^3,z,a,b),
\quad J=3y^3,\quad S=y^6=\theta^*(v^2).
\]

For the fixed physical equation \(F\), the quotient equation satisfies
\(\theta^*G=SF\). Its source is \(B=v^4/3\), and
\(A=y^3=(J/S^2)\theta^*B\).

## Rational-current identity

For any rational quotient vector field \(W\), let

\[
 V=\frac{J}{S}(d\theta)^{-1}\theta^*W.
\]

Written explicitly, with every \(W_i\) evaluated at \(\theta\),

\[
\begin{aligned}
V_x&=3W_u/y^4-xW_v/y^6,&V_y&=W_v/y^5,\\
V_z&=3W_z/y^3,&V_a&=3W_a/y^3,&V_b&=3W_b/y^3.
\end{aligned}
\]

The complete first-jet identity is

\[
A-V(F)+F\operatorname{div}V
=\frac{J}{S^2}\theta^*!
 \left(B-W(G)+G\operatorname{div}W\right).
\]

The scaling correction has not been dropped:

\[
\operatorname{div}V
=\frac{J}{S}\theta^*!left(\operatorname{div}W-2W_v/v\right).
\]

It cancels the matching derivative of \(S\) in \(V(F)\). In particular, a
quotient remainder \(G^2R\) becomes \(F^2J\theta^*R\). The construction
therefore retains nonzero remainders and is not restricted to strict currents.

`verify_piola_transfer.py` checks all 25 independent coefficients of the first
derivatives of \(W\), all five value coefficients, the source coefficient,
the five scaling corrections, and the explicit cleared formulas below using
independent standard-library exact Fraction arithmetic.

## Explicit polynomial witness map

Suppose \(E\ne0\), \(P=(P_u,P_v,P_z,P_a,P_b)\), and \(Q_G\) are
quotient polynomials over \(\mathbb C\) satisfying

\[
B E^2-E\sum_iP_iG_i+
G\left(E\sum_i\partial_iP_i-\sum_iP_i\partial_iE\right)
=G^2Q_G,
\qquad \gcd(E,G)=1.
\]

No degree constraint is imposed at this affine stage. Define

\[
\begin{aligned}
D&=y^6\theta^*E,\\
N_x&=3y^2\theta^*P_u-x\theta^*P_v,&
N_y&=y\theta^*P_v,\\
N_z&=3y^3\theta^*P_z,&
N_a&=3y^3\theta^*P_a,&
N_b&=3y^3\theta^*P_b,\\
Q_F&=3y^{15}\theta^*Q_G.
\end{aligned}
\]

Then the exact physical affine identity is

\[
A D^2-D\sum_iN_iF_i+
F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)
=F^2Q_F.
\]

These are polynomials: the apparent inverse powers of \(y\) in \(V\) have
all cleared. The monomial substitution \(u=xy,v=y^3\) is injective because
\((i,j)\mapsto(i,i+3j)\) is injective on exponent pairs. Hence \(D\ne0\).

## Complex denominator admissibility

The extra factor \(y\) is coprime to \(F\), since \(F|_{y=0}\ne0\).
For the other factor, localize at \(v\) downstairs and \(y\) upstairs:

\[
R=\mathbb C[u,v^{\pm1},z,a,b],\qquad
T=R[y]/(y^3-v)\simeq\mathbb C[x,y^{\pm1},z,a,b].
\]

This is finite free of rank three. If an irreducible element \(\pi\) of
\(T\) divided both \(\theta^*E\) and \(F\), its finite-free norm would
divide both \(E^3\) and \((G/v^2)^3\). That norm is nonunit: a unit norm
would give an inverse for \(\pi\) by the adjugate formula. This contradicts
\(\gcd(E,G)=1\) in the Laurent polynomial UFD \(R\). Thus the pullback
denominator is coprime to \(F\) over \(\mathbb C\). This argument does not
infer complex coprimality from rational irreducibility.

## Homogeneous lift and the six required components

Choose an integer

\[
d\ge\max\left(3,\deg D,\max_i(\deg N_i-1)\right).
\]

With \(t=X_0\), homogenize \(D\) to degree \(d\), each \(N_i\) to
degree \(d+1\), and \(Q_F\) to degree \(2d-6\). The last degree bound
follows from the affine identity: its left side has degree at most \(2d+6\)
and \(F^2\) has degree 12. Zero components are allowed. Insert the zero
\(X_0\)-component and place the other components in the immutable order:

\[
(N_0,N_1,N_2,N_3,N_4,N_5)
 =(0,N_x^h,N_a^h,N_y^h,N_z^h,N_b^h).
\]

All terms of the homogeneous cleared identity now have degree \(2d+6\).
At \(t=1\) they equal the established affine identity; dehomogenization is
injective on a fixed homogeneous degree, so the identity holds identically.
There is no missing \(\partial_t\) correction because \(N_0=0\).
The homogeneous target is exactly \(A_h=t^3y^3\), not \(y^6\) or
\(y^3\). A new factor \(t\) in the denominator is legal because
\(F_h|_{t=0}\ne0\); all other common factors would dehomogenize to an
excluded affine common factor. Thus this gives the precise contract degrees
and complex admissibility, conditional on the quotient identity above.

Equivalently, homogenizing directly in quotient weights
\((t,u,v,z,a,b)=(1,2,3,1,1,1)\), one has

\[
\deg G_h=12,\quad B_h=t^3v^4/3,\quad \deg B_h=15,
\quad \deg(W_u,W_v,W_z,W_a,W_b)=(5,6,4,4,4).
\]

The factor \(t^3\) in the homogeneous source must be retained. These weights
produce a physical rational field homogeneous of degree one under the displayed
Piola formula.

No quotient witness has yet been supplied. These transport formulas alone do
not prove `HasCertificate` and have not been formalized in Lean.
