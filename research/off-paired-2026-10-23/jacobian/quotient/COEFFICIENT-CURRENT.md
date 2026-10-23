# Quartic-normal coefficient current with the actual source

This is an exact sufficient interface. No coefficient field satisfying it has been constructed.

With the coefficient-retaining quotient $u=xy$, $v=y^3$, the actual density is $du\,dv\,dz/3$ and

$$
G=v^2F=v^4+Sv^2+Tv+R,
$$

$$
S=1+z^6+a^6+b^6+uz/2+uab/3,\quad T=u^3zab/2,\quad R=u^6.
$$

The source is exactly $v^4\,du\,dv\,dz\,da\,db/(3G^2)$ on the chart $v\ne0$.

If a rational vector field $W$ in $(u,z,a,b)$, independent of $v$, satisfies

$$
W(S)=S,\quad W(T)=T,\quad W(R)=R,\quad \operatorname{div}W=1,
$$

then

$$
W(G)=G-v^4,\qquad -W(G)+G\operatorname{div}W=v^4.
$$

Thus $W/3$ is a strict rational ambient primitive for this exact source. A nonzero denominator independent of $v$ is coprime to monic $G$ as a polynomial in $v$; transport to the original function field and homogeneous certificate remains necessary.

Writing $E=(u\partial_u+z\partial_z+a\partial_a+b\partial_b)/6$, the remaining construction is a correction $V$ with

$$
V(u)=0,\quad V(zab)=0,\quad V(S)=1+uz/3+uab/6,\quad\operatorname{div}V=1/3.
$$

Indeed $E(T)=T$, $E(R)=R$, $E(S)=S-(1+uz/3+uab/6)$, and $\operatorname{div}E=2/3$. This is a concrete source-carrying constructive obligation, not a primitive supplied by the universal quartic coefficients.

## Boundary of the polynomial model

Every first partial derivative of $G$ vanishes on $u=v=0$. This is a codimension-one singular locus of the fourfold model, so smoothness or Fano arguments cannot be inferred from the quartic presentation before normalization.

Putting $v=q u^3$ gives the boundary branch equation

$$
(1+z^6+a^6+b^6)q^2+(zab/2)q+1=0.
$$

It records the original $y=0$ boundary with $x^3=1/q$. The polynomial source $v^4$ and the clearing factor $v^2$ must be retained through any normalization or polynomial-family construction.

`quartic-coefficient-interface.py` checks all displayed algebraic identities exactly.
