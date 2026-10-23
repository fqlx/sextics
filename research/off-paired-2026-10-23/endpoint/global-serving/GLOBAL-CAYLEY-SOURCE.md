# Full-quotient Cayley quadric and its actual source

This is a global source-retaining incidence and an explicit first current
on its Cayley host. It is not a certificate, and it does not establish a
Fano serving theorem for the target. In particular, the essential ruling
double cover below has not been integrated. Constants in the final
quadric-cylinder transfer have not been calibrated against the physical
residue orientation.

## Full finite quotient

Write `w=X0,x=X1,u=X2,y=Y0,z=Y1,v=Y2` and put

```
a=x^3, b=y^3, q=xy, U=u^3, V=v^3, p=uv.
C1=ab-q^3, C2=UV-p^3,
H0=w^6+z^6+w^3*z*q/2+w^2*q*p/3,
Q=a^2+b^2+U^2+V^2+H0+a*z*p/2.
```

The exact physical F is `Q` after substitution. The quotient by the two
inverse cube-root actions is the weighted complete intersection
`C1=C2=Q=0` in `P(3,3,3,3,2,2,1,1)`. All three equations have degree six.
This is a quotient of the actual fourfold, rather than a separate
coefficient-space variety.

On `w=1`, choose the ordered two-normal residue so that

```
Res_C1,C2(da db dq dU dV dp dz/(C1 C2))
  = da dq dU dp dz/(a U).
```

The Jacobians of `(x,y)->(a,q)` and `(u,v)->(U,p)` are `3a` and `3U`.
Consequently the actual target density is

```
y^3 dx dy du dv dz = b/(9aU) da dq dU dp dz.
```

Thus the physical pole-two form is exactly the above norm residue with
numerator `b/9`; homogeneously its numerator is `w^3*b/9`.

## The global Cayley host

Let `(l:m:n)` be the Cayley coordinates and define

```
Fcal=l*C1+m*C2+n*Q.
```

The hypersurface `Fcal=0` in the product of the weighted projective
seven-space with `P2` is the standard Cayley host. On its smooth stack
locus, adjunction gives `K=O(-12,-2)`. The Gysin incidence
`P2 x {C1=C2=Q=0} -> {Fcal=0}` shifts cohomology by two Tate twists.
Its existence alone does not prove the source has coniveau one: one
would need an additional coniveau step on the relevant host summand.

The standard residue description of the source summand has numerator
proportional to `n*w^3*b` and pole four in `Fcal`. The universal Cayley
factorial is nonzero; its precise orientation and normalization remain
to be bound before using this as an exported source identity. All the
following current identities are literal identities for the displayed
numerator `n*w^3*b`.

View the host as a quadric fibration in `(a,b,U,V)` over
`P(2,2,1,1)_(q,p,w,z) x P2_(l,m,n)`. Set

```
Dl=n^2-l^2/4, Dm=n^2-m^2/4,
S=n*H0-l*q^3-m*p^3,
F0=Dl*S-n^3*z^2*p^2/16,
Se=F0/Dl.
```

The rank-four matrix of its quadratic part has determinant `Dl*Dm`.
The compactified rank-five quadric has determinant `Dm*F0`. The main
discriminant `F0=0` has bidegree `(6,3)` on the weighted three-space
times `P2`. Formal adjunction gives canonical degree `(0,0)`, not a
Fano inequality. Although its equation is linear in `m` and hence the
main discriminant itself is birationally rational on `Dl*p != 0`, the
ruling cover is essential:

```
xi^2=Dl*Dm, F0=0.
```

The double cover of `P2` alone is a rational degree-two del Pezzo
surface (with singularities from its four branch lines). Pulling `F0`
to it gives a family of weighted degree-six surfaces. Neither its
rational base nor the rationality of `F0=0` integrates the anti-invariant
ruling sector.

## Literal source-carrying first current

Complete the square with

```
a0=-n^2*z*p/(4Dl), b0=l*n*z*p/(8Dl),
X=(a-a0) partial_a+(b-b0) partial_b+U partial_U+V partial_V,
T=(-l partial_a+2n partial_b)/(4Dl).
```

Then `div X=4`, `X(Fcal)=2(Fcal-Se)`, `div T=0`, and
`T(Fcal)=b-b0`. If `vol4=da db dU dV`, the three-form

```
P= -n*w^3 i_T(vol4)/(3Fcal^3)
   +n*w^3*b0 [i_X(vol4)/(6Se Fcal^3)
              +i_X(vol4)/(12Se^2 Fcal^2)]
```

satisfies the exact fiber identity

```
d_fiber P=n*w^3*b*vol4/Fcal^4.
```

Wedge with the full five-dimensional base volume. The identity is then
an absolute exterior identity: derivatives of the displayed rational
coefficients in all five base directions wedge to zero. No Cayley
parameter or physical base derivative has been discarded.

This proves exactness on the Cayley ambient complement after allowing
`Dl*F0` as denominators. It does **not** descend a primitive to the
physical fourfold: the inverse Gysin operation meets the new
discriminant pole. The unresolved residue on that pole is the actual
serving obligation.

The coefficient of the critical `i_X(vol4)/Fcal^2` term simplifies to

```
n*w^3*b0/(12Se^2)
  =l*n^2*Dl*z*p*w^3/(96 F0^2).
```

Thus, after the quadric-cylinder residue, the prospective main-cover
source has the shape

```
constant * l*n^2*Dl*z*p*w^3/(xi F0^2)
  * Omega_weighted3 * Omega_P2.
```

This last line records the source character and pole shape; its
nonzero constant, all boundary components and a complete cylinder
transfer have not yet been proved. It is not used as a certificate.

## Character and boundary checks

The physical `Y -> -Y` involution acts by

```
(b,V,q,p,z,l,m)->(-b,-V,-q,-p,-z,-l,-m),
(a,U,w,n)->(a,U,w,n).
```

It fixes `Fcal,Dl,Dm,F0`. Its determinant on the four quadric coordinates
is positive, so it preserves the ruling orientation `xi`; the sign of
the main numerator is negative and is cancelled by that of the base
volume. The physical source is invariant as required. The ruling deck
`xi -> -xi` acts negatively on the main source, so its ordinary trace
to the rational discriminant is zero.

At a generic simple `Dm` branch point away from the other poles,
`Omega_P2/xi` becomes regular after the finite double cover: the
transverse differential supplies the missing square root. This does
not authorize deleting intersections or the projective boundaries.
For example, solving `F0=0` for `m` hides a divisor at `n=0`; it cannot
be used to declare `Dl` a square merely from the even multiplicities
visible in the affine `m` chart.

For context, the full projective diagonal group of the physical sextic
has order 36. The target including its volume is invariant. The
Reid--Tai age calculation on every nonempty fixed eigenstratum gives
ages `1,3/2,2,5/2`, all at least one. Thus the original diagonal quotient
has canonical singularities and torsion canonical class of index two.
It cannot itself be a rationally connected/Fano serving variety.
This does not obstruct a correspondence serving only the target
summand; it explains why a direct dominant Fano cover is insufficient.

`verify_cayley_quadric.py` checks the square completion, both
determinants, the literal source current, the involution characters and
the complete finite age enumeration. No bounded denominator search is
performed.
