# Full cubic graph supports from the Y angle

This is a constructive finite-correspondence support candidate, not a
source primitive or a claimed Gysin calculation.

Write `HX=sum Xi^6`, `CY=sum Yi^6`, and let `M` be the complete mixed part
of the immutable sextic, so `F=HX+CY+M`. Choose two Y coordinates and put

```
T=Yi^6+Yj^6, W=Yi^6*Yj^6.
```

On the finite normalized Fermat cover, `a^6+b^6=1`, the angle product has
`q^6=W/T^2`, and the correct angle differential is `da/b^5`. Its fixed
elliptic quotient is

```
e=1/(a^2*b^2), y=(a^6-b^6)/(a^3*b^3), y^2=e^3-4.
```

Take `gamma^3=4`. The fixed S3 cubic curve has

```
X=gamma/q^2, Y=2*y,
j=(X^3-64)/(4*X^2)=(1-16*q^6)/(gamma^2*q^2).
```

The actual physical normalized cubic has
`j^3=M^3/(HX^2*CY)` (with its finite coefficient roots retained).
Consequently the full graph, rather than merely its differential, has
the degree-54 equation

```
D54=16*W*T^4*M^3-HX^2*CY*(T^2-16*W)^3.
```

Substitution `M=-HX-CY`, valid on the original sextic, gives the exact
factorization

```
D54 = -D18Y*Q36,
D18Y = CY*T^2+16*HX*W,
Q36 = 16*CY^2*T^2*W+48*CY*HX*T^2*W
      -256*CY*HX*W^2+HX^2*T^4.
```

Each of the three held-out Y choices thus gives a degree-18 graph
support. They differ from the three held-out X supports, despite having
the same universal polynomial shape. The equation includes the whole
physical mixed coefficient through `F=0`; it is not the density-only
CM projection.

For completeness, after coefficient roots `h^3=HX`, `c^3=CY` and the
compatible graph branch are chosen, the three normalized cubic roots
are

```
r1=-4*q^2/gamma,
r2=2*q^2/gamma+i*(a^6-b^6)/(gamma*q),
r3=2*q^2/gamma-i*(a^6-b^6)/(gamma*q),
p_k=(h/c)*r_k.
```

They are the complete root components of `p^3+j*p+1`, not just a
scalar-density trace. The graph equation has several branches before
the coefficient and Fermat roots are fixed; tracing or descending must
retain all of those finite deck characters. In particular no component
difference is yet asserted to carry the target residue.

In the constant-density K3 chart `C=Z^2+u^6+v^6`, the first CM factor
arises from this same Y angle: `q^6=u^6*v^6/(u^6+v^6)^2`. Both H and C
are independent of the normalized angle. This is why these supports
are naturally exposed by that chart. The remaining obligation is an
actual normal/source Gysin calculation or exact rational current on
their components.

Prepared with OpenAI Codex assistance.
