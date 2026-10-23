# The pure-component kappa restrictions

This concerns only two sufficient restrictions of the new cubic-ray
rank-two current. It is not an obstruction to that complete current or to
the immutable certificate. It is distinct from the newly published old
three-base contact-current obstruction.

Let `kappa=B^3/(CH^2)` in the original cubic-ray base `(x,a,u,v)`. A field
`A` with `div(A)=0` and `A(log(kappa))=-1/(2HC)` would imply

```
div(kappa*A)=-B^3/(2H^3C^2).
```

Likewise a pure-W current requires `Bvec(log(kappa))=0` and
`div(Bvec)=1/(HC)`, implying

```
div(kappa*Bvec)=B^3/(H^3C^2).
```

Both therefore require rational exactness of
`Psi=B^3/(H^3 C^2) dx da du dv`.

Homogenize on `P2_X x P2_Y` with coordinates `[t:x:a]`, `[w:u:v]`:

```
H=t^6+x^6+a^6, C=w^6+u^6+v^6,
B=t^3*x*u*w/2+x^3*a*u*v/2+t^2*x*a*v*w/3,
Psi=t^3*w^3*B^3 OmegaX OmegaY/(H^3 C^2).
```

The two Fermat curves are smooth and proper. Projecting the numerator
to the `(u,v)` exponent character `(3,3)` modulo six selects exactly

```
t^3*x^9*a^3*w^3*u^3*v^3/8.
```

At H pole three use the Jacobian multiplier `t^3*x^4*a^3/6` of `H_x`.
Its divergence divided by two gives `t^3*x^3*a^3/3` at H pole two. Thus
the proper iterated residue has a nonzero Hodge `(0,2)` component with
the explicit product Jacobian-ring coefficient

```
(1/24)*(t^3*x^3*a^3) tensor (w^3*u^3*v^3).
```

Both degree-nine monomials are nonzero in the Fermat Jacobian quotients,
whose generator ideals are the fifth powers of the three coordinates.
No other source term has the selected Y character, so it cannot cancel.
A proper H2 class on the product of the curves can vanish on a nonempty
open set only through divisor classes, of type `(1,1)`. Its nonzero
`(0,2)` component therefore cannot be rationally exact. Algebraic
residue commutes with differentiation, so Psi is not rationally exact.

This excludes both pure-component restrictions with arbitrary rational
poles. Normalized field trace extends the exclusion to finite algebraic
extensions. The full two-component system remains open and must retain
both current vectors.

The finite-extension statement concerns the displayed explicit linear
constraints on A or Bvec. It does not classify every scalar-looking
current on a selected cubic sheet: after adjoining p, its evaluated
scalar functions need not be independent over the enlarged coefficient
field, whereas the base-changed rank-two differential module still has
rank two. No broader scalar-current exclusion follows from this argument.

The closed-time construction also lies in the excluded pure-W restriction:
for `lambda=dlog(kappa)` and a relative-closed eta with
`eta(CH*X_log(kappa))=1`, the base three-form
`chi=theta_form wedge lambda wedge eta` obeys
`d chi=Omega/(HC)` and `lambda wedge chi=0`. Consequently
`d(kappa*chi)=Psi`, the same contradiction. This includes eta with
arbitrary rational kappa coefficients and finite-cover eta; no further
closed-time searches are warranted.

`pure_kappa_moment.py` checks the five small exact numerator/Jacobian
identities. An independent 31-check Fraction audit passed the gauge,
moment normalization, selected character and coefficient, and actual
source binding; it also reviewed the residue/localization and finite-trace
scope argument. See `../../../audit/cubic-ray/verify_pure_component_fraction.py`.
No protected Lean verification is claimed.
