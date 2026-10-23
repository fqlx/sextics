# The actual source on the J=1 elliptic support candidate

Status: an exact elliptic/Prym source decomposition and an explicit
coefficient primitive for the elliptic component. A closed mixed Gysin
current for the full source has not been constructed. This does not serve
the complementary Prym component or establish a sextic certificate.

No earlier J=1 support calculation was found in the research handoff. The
existing moving-endpoint elliptic quotients are different constructions.

## The involution and the actual normal source

Use the normalized canonical curve

```
ab t=q³,
Q=a²+b²+t²+cq²+d a q+e q t=0,
d=m+n, e=m−n.
```

On the chosen J=(d/e)²=1 component n=0, the involution exchanges a and t.
Its projective determinant is −1. Consequently the invariant canonical
holomorphic form corresponds to the numerator a−t, while the actual
numerator b is anti-invariant and belongs to the three-dimensional Prym.

In the q=1 chart put

```
s=a+t, zeta=a−t, Y=2s+m,
s²+m s+b²+c−2/b=0,
zeta²=s²−4/b.
```

Calibrating to the original convention `eta_b=b dq/J` in the t=1 chart
gives

```
eta_b=+db/[zeta Y].
```

The elliptic quotient is

```
W=bY,
W²=−4b⁴+(m²−4c)b²+8b.
```

The actual source coefficient is tau=−partial_e eta_b, not eta_b itself.
For the horizontal lift holding b fixed, its two involution projections are

```
tau_plus=+db/Y³=b³db/W³,
tau_minus=−(s³+2m/b)db/[zeta³Y³].
```

Indeed `partial_e=(partial_m−partial_n)/2`. The tangent derivative of the
anti-invariant eta_b stays in the Prym; its odd normal derivative enters
the invariant elliptic factor. The displayed plus component equals
`partial_n eta_b/2`. Both components are nonzero generic rational forms.

## Literal comparison with the original source representative

Changing the held fiber coordinate changes the representative by an exact
fiber term. Set

```
J_a=2a²+d a−2b²,
D1=a(2a+d)−t(2t+e),
H=b t/(J_a D1).
```

The source in the original fixed-q lift and the fixed-b source satisfy

```
tau_actual=tau_fixed_b−d_b H.
```

Thus the two actual projections also include `−d_b H_plus` and
`−d_b H_minus`, where H_plus=(H+sigma H)/2 and
H_minus=(H−sigma H)/2 on n=0. Both rational potentials are serialized in
`j1-source-projection-results.json`. No moving-coordinate term is dropped.

## A source-carrying elliptic primitive

Set

```
u=1/b, y=W/b², lambda=m²−4c,
y²=8u³+lambda u²−4.
```

Then the actual elliptic source is

```
tau_plus=−u du/y³.
```

The marked-section differential

```
psi=du/(u y)
```

has constant finite residues ±1/(2 sqrt(−1)) at u=0,y=±2sqrt(−1), no
infinity residue, and satisfies the literal identity

```
tau_plus=2 partial_lambda psi.
```

Its full compact class, with Delta=lambda³−1728, is

```
tau_plus=(12lambda/Delta)du/y+(144/Delta)u du/y
 +d_u[(lambda²−12lambda u−288u²)/(Delta y)].
```

Thus this route carries the actual elliptic source and supplies both its
rank-two class and an explicit algebraic normal-function derivative. It
does not turn an arbitrary physical coefficient times tau_plus into an
exact form: the derivative of that coefficient times psi remains.

For example, retaining the entire normalized physical density H_D on the
support, `dc dd de=−2 dc dm dn` and `lambda=m²−4c` give the leading normal
elliptic source

```
(H_D/2) tau_plus wedge d_lambda wedge dm wedge dn
 =H_D partial_lambda(psi) wedge d_lambda wedge dm wedge dn.
```

A tangent lambda current therefore leaves
`−partial_lambda(H_D) psi` with its marked-section residues, as well as the
displayed exact-fiber correction. Normal derivatives away from n=0 and
the full Prym source also remain. This is a first normal source identity,
not a global current or a closed Gysin residue.

## The physical support and CM cover retain every coefficient

Before normalizing square or sixth roots, J=1 is

```
1+r²=k²T, T=1+z⁶, B=1+k⁶/r².
```

The physical involution is rational: a maps to t/k and t maps to k a.
With S=k a+t and q=1, its quotient has the coefficient-retaining equation

```
Wphys=b(2T S+z/2),
Wphys²=−4TB b⁴+(z²/4−4kT/3)b²+8kT²b.
```

Adjoin rho²=1+z⁶. The physical conic base has the explicit parameterization

```
k=(rpar+rpar^−1)/(2rho),
r=(rpar−rpar^−1)/2.
```

Thus this cover of the support base is the genus-two CM curve in (z,rho)
times a rational parameter line. The deck involution also acts on rpar,
so descent must be checked. The elliptic quotient still has its full
rpar,z dependence; the CM factor alone does not prove that a proposed
mixed elliptic/base two-form is closed.

A successful Gysin construction must now provide a closed mixed
two-form on this actual support, its full normal source identity, the
physical density and normalizers, and currents for the complementary
Prym components. None of these obligations is replaced by quotient
existence or the coefficient primitive above.

`verify_j1_source_projection.py` passes twelve exact quotient, source,
Cartan, rank-two reduction, physical coefficient, and CM conic identities.
