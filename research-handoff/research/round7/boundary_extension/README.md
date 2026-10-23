# Moving fixed-j0 cover: exact boundary charts and elliptic target

This folder contains independent exact audits and a concrete elliptic target for
the moving fixed-j0 slope surface. It contains no off-paired certificate.

The coordinates are `alpha=s/v=U^2`, with the three slope equations from
`../moving_j1728/legendre_model.pickle`. The normalized boundary at `v=0`
has equation, up to a nonzero constant,

```
U_tilde^6=P(q)G(q)^2,   U_tilde=J(q)^2 U,
J=1+q^6,               P=11664 J^4-q^6.
```

## Exact charts

`conductor_normalization.py` works over `QQ[q]/(G)` and recomputes the
second implicit jet. Its exact output is `4AC-B^2=0`, and `A` is a unit.
This is sufficient for the asserted normalization, not merely a heuristic
based on a vanishing leading discriminant: modulo `alpha^3`, the first two
equations depend only on `z=alpha*v`. After eliminating `h,t`, the critical
value in the `q` direction is therefore divisible by `alpha^3`. The
parametric Morse lemma gives

```
F=L(q,alpha,v)^2+alpha^3 T(alpha,v),  T(0,0) != 0.
```

After `alpha=U^2`, normalization separates the two smooth formal sheets
`L=+-U^3 sqrt(-T)`. Their coordinates are `(U,v)`; `v` has normal order zero
at conductor roots.

`other_normal_charts.py` directly rescales the original equations and checks
nonzero implicit Jacobians. The charts are:

* At `q=0`: `h=q^3 H`, `v=q^3 n`; `alpha,t` stay finite.
* At infinity, `z=1/q`: `h=z^9 H`, `v=z^3 n`; `alpha,t` stay finite.
* At `J=0`: `h=H/J^2`, `alpha=A/J^4`, `t=T/J^4`; `v` stays finite.

The first two limiting systems agree, with boundary values
`H=1/54`, `t=5/81`, `alpha^3=16/(531441 ell)` and Jacobian
`128 ell alpha^2/3`. At `J=0` the Jacobian is likewise nonzero.

The P-root chart is independently checked by cycle/reflection in
`../moving_j0_audit/P_normalization_chart.py`. There the correct order is
`v=U^10 n`. Consequently the old five dual first-jet test sections are polar
there, and the previously computed rank-five pairing does **not** obstruct
extension. Its six-dimensional kernel is not a list of proven global forms.
The full conormal degree estimate is 276, exceeding the boundary canonical
degree 204. This local fact does not imply global irregularity.

## Concrete genus-one target

The invariant boundary quotient has `u=1+q^6`, `y=xi` and

```
y^2=11664 u^4-u+1.
```

`elliptic_target.py` exactly verifies the transformation

```
X=(2(y+1)-u)/u^2,
Y=((X^2-46656)u+X)/2,
Y^2=X^3-46656X+11664,
dX/Y=-6q^5 dq/xi.
```

Its j invariant is `191102976/110591`; the curve is not the fixed j=0
elliptic quotient used in the incidence. On the boundary,

```
xi=(918330048 i/ell) J^6 U^3/G.
```

This provides an explicit target for a rational-map/Mordell--Weil lift. No
global point on this elliptic curve over the full slope-surface function
field has been found. Keeping `u=1+q^6` would demand a global square root of
`P(q)`; the norm and monodromy calculations rule out that simplest lift.
A successful map must change `u` away from the boundary, or a global closed
one-form must be constructed by another method. A nonzero boundary
restriction alone does not establish global extension or the required
Gysin equality with the physical off-paired source.
