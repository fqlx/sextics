# Eight-plane: an actual quartic-root source and Ferrari transfer

This is mathematical progress toward `eight-plane-configuration`, not a solve.
The exact instance is bound in `model.py` against `instance.rec`, including its
SHA256 in `model.json`.  No repository files were changed.  The live discussion
was read and was empty when this route was started.

## Exact source chart

Write `U=X+iY`, `V=X-iY`.  The selected disjoint planes are `U=0` and `V=0`.
Set

```
U=k*z*(1,u1,u2),   V=k*(1,v1,v2),
X=(U+V)/2,         Y=(U-V)/(2i).
```

With the prescribed original variable order `(X0,X1,X2,Y0,Y1,Y2)`, the full
Jacobian in `(k,z,u1,u2,v1,v2)` is `i*k^5*z^2/8`.  Contraction with the Euler
field is contraction with `k*d/dk`, so the projective volume on `k=1` is
`i*z^2/8 dz du1 du2 dv1 dv2`.  Direct substitution in the exact record gives

```
F=z*G(z),       deg_z G=4,
A=i*(z^2-1)^3/64,
A*Omega/F^2 = -(z^2-1)^3/(512*G^2) dz wedge d^4base.
```

The physical quartic coefficient term counts are `(45,72,82,72,45)`; they are
saved, without expanding discriminants, in `model.pickle`.  The global sign
involution exchanges the planes, giving `G(z;u,v)=z^4*G(1/z;v,u)`.

The actual normal deformation must move the planes:

```
F_eps=z*G + eps*i*(z^2-1)^3/64.
```

The source above is exactly minus its derivative in the simple-pole density
`i*z^2/(8*F_eps)`.  Treating this as a deformation of a fixed quartic with
unchanged leading/base factors would lose terms.

## Hermite primitive and tracezero residue

For `N=(z^2-1)^3`, the universal script finds the unique `deg P<=3`, `deg B<=2`
satisfying

```
N=P'*G-P*G'+B*G,
N/G^2 dz=d(P/G)+(B/G)dz.
```

The seven explicit universal coefficients are in `hermite.json/pickle`.
They have quartic-discriminant denominators; the primitive also has the chart
leading coefficient in its denominator.  Wedging with the four passive base
differentials makes this an exact correction of the full five-form: the other
derivatives of `P/G` wedge to zero.

At a quartic root the remaining source is

```
rho=B/G'=(N'*G'-N*G'')/(G')^3,
actual residue = -rho/512 * d^4base.
```

Lagrange's trace formula gives `Tr(rho)=[z^3]B/g4=0`.  Thus the three
coefficients of `B` are the source vector in the tracezero basis
`(1/G', z/G', z^2/G')`.  The power-basis version is computed by the four-by-four
matrix for multiplication by `G'`, whose determinant is `Disc(G)/g4^2`.

## Ferrari correspondence: keep the quadratic twist

Depress and normalize the quartic, writing

```
G/g4=t^4+p*t^2+q*t+r,
rho(t)=a0+a1*t+a2*t^2+a3*t^3,
4*a0-2*p*a2-3*q*a3=0.
```

On an oriented pair of distinct roots put `w=t_i+t_j`, `y=w^2`.  Then

```
R(y)=y^3+2*p*y^2+(p^2-4*r)*y-q^2=0,
w^2=y,
rho(t_i)+rho(t_j)=w*f(y),
f(y)=a1-q*a2/y-(y+3*p)*a3/2.
```

On `q!=0` the polynomial representative of `f` is

```
f0=a1-3*p*a3/2-a2*(p^2-4*r)/q,
f1=-a3/2-2*p*a2/q,
f2=-a2/q.
```

The inverse, including its normalization, is

```
rho(t_i)=1/2 * sum_{j!=i} (t_i+t_j)*f((t_i+t_j)^2).
```

These are generic identities, verified with independent labeled roots in
`hermite.py`.  They define a common-flag degree-12 correspondence: degree three
over the quartic-root cover and degree two over the oriented-pair cover.
Trace commutes with differentiation, so the identities transfer primitives
and preserve the entire standard rank-three sector.  Taking ordinary trace
to the cubic resolvent alone would discard that sector.  Retaining the
quadratic character `w` is essential.

For a base derivative, the charged line over the cubic algebra has connection

```
nabla_i u = partial_i u + (partial_i y)/(2*y)*u,
partial_i y = -(partial_i R)/R_y.
```

Thus the explicit rational-current target is

```
sum_{i in (u1,u2,v1,v2)} nabla_i u_i = -f(y)/512.
```

`source.pickle` contains the source arithmetic circuit, physical substitution,
and universal three-by-three connection matrices in `(p,q,r)` for the basis
`(w,w*y,w*y^2)`.  The circuit avoids expanding huge physical rational
functions.  All arithmetic is over the original function field with `i`
adjoined for the fixed linear chart; the finite trace inverse allows descent.

## Reproducible nonzero fiber

At `(u1,u2,v1,v2)=(1,2,3,5)`, modulo 101:

```
G = 72+85z+23z^2+2z^3+37z^4,
P = 75+91z+69z^2+88z^3,
B = 34+83z+58z^2,
rho = 49+30z+74z^2+93z^3,
(p,q,r)=(81,48,6),
R = y^3+61y^2+73y+19,
f = 96+35y+27y^2.
```

Both quartic and cubic are squarefree.  A separate FLINT computation verifies
the Hermite identity and tracezero condition at this physical fiber.  The
source factor is still `-1/512`; `f` is nonzero.

Run `python model.py`, `python hermite.py`, `python source.py` to reproduce.

## Limits and next constructive step

Rational P1 fibers do not prove coniveau.  No rational current solving the last
equation, serving divisor, or global correspondence with the required Gysin
image has been constructed.  The denominators introduced by Hermite reduction
must be retained in any eventual proof.  This packet provides the actual
source and an invertible finite correspondence, so a proposed primitive can
be checked and transferred without losing a character or a scale factor.
