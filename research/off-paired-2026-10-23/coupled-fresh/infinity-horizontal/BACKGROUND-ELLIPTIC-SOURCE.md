# Actual background source in two elliptic factors

This is a source-retaining geometric interface for constructing a primitive.
No primitive or Picard claim is established by this decomposition.

On X0=1 use x=X1,y=Y0,z=Y1 and

```
H=1+x⁶+y⁶+z⁶+xyz/2,
a=x³,q=xy,b0=q³/a=y³,
C=q/3+za/2,
K0=1+z⁶−H.
```

At fixed H,z the actual background curve is

```
a⁴+a²(K0+zq/2)+q⁶=0.
```

Put s=a+b0 and d=a−b0. Then

```
E+: s²=2q³−(z/2)q−K0,
E−: d²=−2q³−(z/2)q−K0,
a=(s+d)/2, b0=(s−d)/2,
C=q/3+z(s+d)/4.
```

The full background curve is the V4 fiber product of these two double covers
of the q line. Generically the two cubics have three distinct disjoint finite
roots and share only the branch at infinity. The degree-four cover then has
seven inertia-two branch points. Riemann–Hurwitz gives genus four.
The third nontrivial V4 quotient has

```
w=s d=a²−b0²=2a²+K0+zq/2,
w²=(K0+zq/2)²−4q⁶,
```

and genus two. The two elliptic factors are the anti-character factors for
the involution `(a,b0)->(−a,−b0)`. This does not split the separate generic
compact endpoint genus-two Jacobian.

## Exact immutable-target source

The Jacobian in the original physical coordinates is especially simple:

```
partial(H,q)/partial(x,y)=6(x⁶−y⁶)=6sd.
```

Consequently, with the displayed orientation,

```
y³ dx wedge dy=(1/12)(1/d−1/s) dH wedge dq.
```

Equivalently the previous actual normal coefficient phi=q³/P_a satisfies,
on the background curve at fixed H,z,

```
phi dC=(dq/12)(1/d−1/s).
```

For verification, let Paq be partial_a P holding q,H,z fixed. Then
`Paq=2a(2a²+K0+zq/2)=2asd` and
`dC=P_a d q/(3 Paq)`, where P_a holds C,H,z fixed. Thus
`phi dC=q³ dq/(6asd)=(dq/12)(1/d−1/s)`.

The full physical background volume is therefore

```
y³ dx wedge dy wedge dz
 =(1/12) dH wedge (dq/d−dq/s) wedge dz.
```

For the compact endpoint basis omega_j=p^j dp/Z, the actual source is

```
−(1/72) [nabla_H|C omega0]
         dH wedge (dq/d−dq/s) wedge dz.
```

Both elliptic components are present. The derivative `nabla_H|C` keeps the
endpoint parameter C fixed; after changing coordinates C is the full
`q/3+z(s+d)/4` and all its mixed derivatives must be restored.

## Constructive surface to investigate

Fixing H,z gives a new two-dimensional source-carrying fiber: the compact
endpoint genus-two family

```
Z²=(H+C p)²−4p⁶,
C=q/3+z(s+d)/4,
```

over this genus-four elliptic fiber product. This is not one of the 65
fibrations fixing two original coordinate ratios. The older fixed-C curve
and the fixed-C CM K3 are different constructions. The coefficients remain
coupled to both s and d, so the differential split alone supplies no rational
primitive or automatic exact trace.

A positive continuation should construct a relative Picard correspondence
or a literal current for this actual surface and source, retaining the
q dependence of C and all parameter H,z corrections. Nine exact symbolic
source and map checks pass in `verify_background_elliptic_source.py`.

## Canonical model and two trigonal pencils

There is a second concrete model suitable for correspondences. In ordinary
projective coordinates `(a,b0,q,t)` the background curve is the complete
intersection

```
Q=a²+b0²+(z/2)q t+K0t²=0,
G=a b0 t−q³=0.
```

For a generic smooth fiber this is its canonical (2,3) model in P³. At z≠0
the quadric is smooth: its determinant is −z²/16. It has the explicit split
presentation

```
(a+i b0)(a−i b0)=t[−(z/2)q−K0t].
```

Its two rulings supply trigonal pencils. On t=1 their functions can be
represented by `f±=a±i b0`. For fixed f=f+ the remaining q satisfies

```
4i f²q³+(K0+zq/2)²−f⁴=0.
```

The physical parameter
`C=(q/3+za/2)/t` is a canonical hyperplane pencil, generically degree six.
These algebraic presentations do not identify a Picard correspondence by
themselves. The full endpoint parameter remains the same linear form on
the canonical curve; replacing it by a trigonal parameter requires all
mixed derivatives and cover sheets to be restored.
