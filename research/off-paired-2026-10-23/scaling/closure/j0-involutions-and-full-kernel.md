# Explicit elliptic involutions with the full endpoint kernel retained

This is source transport and finite-correspondence algebra, not a primitive.

Fix \(L=H-3zC/2\) and \(z\), and put

\[
b=3z^2/4,\quad B=L-1-z^6,\quad
w=y^2/x,\quad T=x^3,\quad q=xy,
\quad R=2T+w^3-b.
\]

On the actual genus-four base quotient,

\[
T^2+(w^3-b)T-B=0,\quad q^2=Tw,
\quad R^2=(w^3-b)^2+4B,
\quad C=zT/2+q/3.
\]

The actual source one-form is
\(\rho=-dx/(6y^2)=w\,dw/(6R)\).

## Additional explicit j=0 quotients

Adjoin \(\delta^2=-B\). The involution

\[
j:(w,R,q)\longmapsto(w,-R,\delta w/q)
\]

commutes with \(\tau:q\mapsto-q\). Set

\[
Q_\pm=q\pm\delta w/q.
\]

Then

\[
Q_\pm^2=w(b\pm2\delta-w^3),\qquad
Q_+Q_-=wR.
\]

Thus the quotients by \(j\) and \(\tau j\) are explicit elliptic curves.
Under \(X=1/w,Y=Q_\pm/w^2\), they have

\[
Y^2=(b\pm2\delta)X^3-1,
\]

so their generic j-invariant is zero. The source \(\rho\) is anti-invariant
under both involutions and invariant under \(\tau\). Its unweighted trace
to either new elliptic quotient is zero. The known two variable-j elliptic
factors carry \(\rho\) itself.

## The beta kernel in the j correspondence

Write \(k=3z/2\), \(d=p+k\), and let

\[
\beta(C)=\frac{dp}{d\sqrt{(L+dC)^2-4p^6}}.
\]

The involution sends

\[
T\mapsto T'=\delta^2/T,\quad q\mapsto q'=\delta w/q,
\quad C\mapsto C'=zT'/2+q'/3.
\]

Both \(C\) and \(C'\) must be retained. Their symmetric functions descend
to the j=0 quotient:

\[
A=C+C'=z(b-w^3)/2+Q_+/3,
\]

\[
P=CC'=z^2\delta^2/4+z\delta Q_+/6+\delta w/9.
\]

Moreover the actual weighted source difference is

\[
\rho(C'-C)
=-\left(\frac{zw}{12}+\frac{w^2}{18Q_+}\right)dw.
\]

Let \(Z^2=(L+dC)^2-4p^6\), \(Z'^2=(L+dC')^2-4p^6\), and work on the
joint finite cover with \(Y=ZZ'\), \(S=Z+Z'\). The source trace in this
correspondence is exactly

\[
\rho\,[\beta(C)-\beta(C')]
=-\left(\frac{zw}{12}+\frac{w^2}{18Q_+}\right)
\frac{2L+dA}{YS}\,dw\wedge dp.
\]

Here

\[
Y^2=(L^2+dLA+d^2P+4p^6)^2
       -4p^6(2L+dA)^2,
\]

\[
S^2=(2L+dA)^2-2(L^2+dLA+d^2P)-8p^6+2Y.
\]

The \(Y,S\) factors depend on the elliptic coordinate and on \(p\).
Therefore this is not yet a rational scalar differential on the j=0
elliptic curve with constant passive coefficients. The full ordinary trace
including the independent endpoint hyperelliptic deck is zero. A source
primitive requires these remaining multiquadratic characters as well.

## Endpoint scaling test

The endpoint modulus is \(I=C^3/(L+kC)^2\). For the j pair,

\[
C'^3(L+kC)^2-C^3(L+kC')^2
=(C'-C)\bigl[(LA+kP)^2-L^2P\bigr].
\]

The factor in brackets is generically nonzero (its reduced leading
\(w^6\) coefficient is \(L^2z^2/4\)). Thus the new base involution does
not directly transport the endpoint by weighted scaling at fixed L,z.

There is an explicit larger correspondence preserving a different fibration:

\[
T'=t^6\delta^2/T,\quad y'^3=t^6\delta y^3/T,
\quad q'=t^4\delta q/T,\quad z'=t^3z,\quad\delta'=t^6\delta.
\]

It preserves \(\chi=z^2/\delta\), with
\(L'=1+t^{18}z^6-t^{12}\delta^2\). Imposing
\(C'^3H^2=C^3H'^2\) gives a degree-36 equation for t, after which the
endpoint scaling factor is rationally
\(\lambda=H'C/(HC')\). Exchanging the two points sends \(t\) to \(1/t\).
This is a concrete finite correspondence on an \((I,\chi)\) fibration;
its source Jacobian and support projector remain unproved.
