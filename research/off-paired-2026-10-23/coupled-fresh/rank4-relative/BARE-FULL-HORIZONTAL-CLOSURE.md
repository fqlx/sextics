# Full bare-coordinate current with genuine horizontal directions

This is a complete scalar reconstruction for the compact rank-four module.
It is not a rational solution of the forcing equation. It retains independent
a and z currents; setting both to zero recovers an already excluded relative
primitive and is not an open construction target.

Use the actual coordinates `(a,C,z)` with

    a=x^3, q=3C−3az/2=xy,
    H=a^2+q^6/a^2+z^6+qz/2+1,
    delta=partial_C|a,z, h=delta H,
    N=3H−2Ch=3Hr, r=1−2Ch/(3H).

All bare derivatives below differentiate this actual H. Explicitly,

    h=18q^5/a^2+3z/2,
    H_a=2a−2q^6/a^3−9zq^5/a^2−3z^2/4,
    H_z=6z^5+q/2−3az/4−9q^5/a.

The physical source density becomes exactly

    y^3 dx dy dz=(q^3/a^2) da dC dz.

There is no inverse P_a in these coordinates.

## Bare cyclic basis

Let t_j=nabla_delta^j omega0, j=0,1,2,3. Define the actual monic scalar
operator by

    t4=d0 t0+d1 t1+d2 t2+d3 t3,
    Lhat=delta^4−d3 delta^3−d2 delta^2−d1 delta−d0.

Its coefficients are rational in `(a,C,z)`. They can be constructed directly
from `M_delta=M_C+h M_H` using four derivative/matrix recurrences. The cyclic
determinant in the original compact basis is

    r^6 * [−16533720 C^2 H^4/(4C^6−729H^4)^3].

The universal Euler relation gives the especially simple exact identities

    delta omega0=r nabla_C omega0−2h omega0/(3H),
    nabla_H omega0=−2(t0+C t1)/N.

Thus a genuine bare-coordinate a-current U t0 and z-current W t0 have compact
columns

    nabla_a(U t0)=(partial_a U−2H_a U/N)t0−2C H_a U t1/N,
    nabla_z(W t0)=(partial_z W−2H_z W/N)t0−2C H_z W t1/N.

The scalar reductions of these columns are therefore

    A_a(U)=partial_a U+2C delta(H_a U/N),
    A_z(W)=partial_z W+2C delta(H_z W/N).

These are the actual horizontal couplings, not artifacts from a transverse
coordinate change.

## Complete Pa-free scalar equation

Put

    F=q^3/(3a^2 N),
    S0=−C delta(F)=−C/(3a^2) delta(q^3/N).

Then the original source is exactly

    −q^3 nabla_H omega0/(6a^2)=F(t0+C t1).

Subtracting the explicit C-current `C F t0` leaves `S0 t0`. Consequently
an actual full compact current is equivalent to a rational solution of

    −Lhat* G + partial_a U + partial_z W
       +2C delta[(H_a U+H_z W)/N] = S0,

where the ordinary formal delta-adjoint is

    Lhat*G=delta^4 G+delta^3(d3 G)−delta^2(d2 G)
             +delta(d1 G)−d0 G.

All four compact components and all three bare physical directions occur.
There is no P_a denominator in the forcing or in the horizontal operators.

## Explicit full-current reconstruction

For any actual solution `(G,U,W)`, write P=H_a U+H_z W and set

    v3=G,
    v2=−delta G−d3 G,
    v1=delta^2 G+delta(d3 G)−d2 G,
    v0=−delta^3 G−delta^2(d3 G)+delta(d2 G)−d1 G+2C P/N.

The a- and z-current columns are `(U,0,0,0)` and `(W,0,0,0)` in the bare
cyclic basis. The C-current is v with the further explicit term `C F t0`.
Their full covariant divergence is the exact original source above. Closure
uses the companion relation in every row; no second-kind component is
omitted.

Conversely every compact four-component current can be compressed into this
form by scalar cyclic reduction and absorption of the discarded terms into
the C-current, exactly as in `SCALAR-HORIZONTAL-CLOSURE.md`.

To return to `(x,y,z)` coefficient currents, the actual Piola transformation
for any bare vector V is

    Vphys_x=(x/3) V_a,
    Vphys_y=3x^2 V_C−C_x V_a−3x^2 C_z V_z,
    Vphys_z=x^3 V_z,
    C_x=3x^2 z/2+y/3, C_z=x^3/2.

Exact fiber Dwork corrections and the final immutable-target certificate
transport remain necessary after a solution is found.

## Scope of the bare-C ODE

With U=W=0, solving `−Lhat*G=S0` would give a relative primitive keeping a,z
fixed, hence keeping `X1/X0,Y1/X0` fixed after finite extension. This is one
of the existing 65 relative scopes. The coordinate-transport corrections in
`ADJOINT-TRANSPORT.md` do not change that fact. Genuine independent U or W
is essential to a new construction.
