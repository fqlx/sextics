# A target-character exceptional surface on the Y graph

This constructs an actual holomorphic two-form on an exceptional surface.
It does **not** yet extend that form over the full graph divisor, compute
its Gysin image, or give a primitive for the target.

## Exact weighted normal model

Choose graph pair `(Yi,Yj)` and held-out `Yk`. Near the Fermat curve
`Y=0,HX=0`, put `Y=epsilon*(a,1,b)` in that coordinate order. Write

```
CY=epsilon^6*C0, C0=a^6+1+b^6,
M=epsilon^2*M0,
M0=mij*a+mjk*b+mik*a*b.
```

On the original sextic, `HX=-epsilon^2*M0-epsilon^6*C0`. The graph
divisor is exactly

```
D18Y=epsilon^14 *
 [epsilon^4*C0*((1+a^6)^2-16*a^6)-16*a^6*M0].
```

Set `epsilon=t^3`, `a=t^2*A`. Then `D18Y=t^54*S`, where

```
S=(1+b^6+t^12*A^6)*((1+t^12*A^6)^2-16*t^12*A^6)
  -16*A^6*(mjk*b+t^2*A*(mij+mik*b)).
```

The ambient fourfold simultaneously has

```
HX=-t^6*(mjk*b+t^2*A*(mij+mik*b))
   -t^18*(1+b^6+t^12*A^6).
```

The residual chart deck group is `t -> omega*t,A -> omega*A`.
Its exceptional surface therefore uses `w=4*A^3*b`, with exact equation

```
HX=0, mjk(X)*w^2=b^7+b.
```

It is dominated by the product of the two curves

```
Cprime: HX=0, xi^2=mjk(X),
G: y^2=b^7+b,
```

via `y=xi*w`, with simultaneous sign quotient. No assertion about an
isotrivial extension to `t!=0` follows from this degeneration.

## Explicit j=1728 factors and a target-character two-form

Take `(Yi,Yj,Yk)=(Y0,Y1,Y2)`, so `mjk=X1^3*X2/2`. On `X1=1`, set
`x=X2,z=X0`, whence

```
z^6+x^6+1=0, xi^2=x/2.
```

The following maps include the whole elliptic curves, not just their
differentials:

```
Cprime -> E_C: UC=8*xi^6=x^3,
                   VC=2*sqrt(2)*i*xi^3*z^3,
                   VC^2=UC^3+UC;

G -> E_G: UG=b^3, VG=b*y,
          VG^2=UG^3+UG.
```

Both curves have `j=1728`. Their differentials satisfy

```
dUC/(2VC)=3*xi*dx/(sqrt(2)*i*z^3),
dUG/(2VG)=3*b*db/(2*y).
```

Consequently their exterior product descends under the simultaneous
sign quotient and is a nonzero constant times

```
gamma=dx wedge db/(z^3*A^3)
     =4*b*dx wedge db/(z^3*w).
```

It is holomorphic on a resolution of the product quotient: upstairs it
is the product of two holomorphic elliptic differentials, and the only
fixed point quotient singularities are rational double points.

It also has the correct invariant character for the two original G36
generators. With `z=X0,x=X2` in the `X1=1` chart:

* `(X2,Y2)->(zeta*X2,zeta^-1*Y2)` gives
  `(x,b,w)->(zeta*x,zeta^-1*b,zeta^-1*w)` and fixes `gamma`.
* `(X1,Y0)->(omega*X1,omega^2*Y0)`, followed by restoring `X1=1`, gives
  `(x,z,b,w)->(omega^2*x,omega^2*z,b,omega^2*w)` and also fixes `gamma`.

Thus there is a specific nonzero exceptional H20 class with the target
symmetry. This symmetry is necessary, not a source/Gysin identification:
the invariant degree-six source space has dimension twenty-four.

## The actual target normal jet

For a chart with an original X coordinate `r` as the hypersurface normal,
`A=X0^3*Y0^3` independent of `r`, the exact ordered double-pole residue is

```
A*Frr/Fr^3 * d(other X) wedge dY0 wedge dY1 wedge dY2
```

up to the stated coordinate permutation sign. In the chart `X1=1`, one
may take `r=X0=z`; here the derivative of `A=z^3*Y0^3` must also be kept,
so the exact coefficient is instead

```
(A*Fzz-Az*Fz)/Fz^3.
```

At `Y=0` this becomes `Y0^3/(18*z^8)`, since
`Fz=6*z^5,Fzz=30*z^4,Az=3*z^2*Y0^3`. Thus the above target graph chart
has leading normal source, up to coordinate orientation,

```
(1/6)*t^25*A^3/z^8 * dx wedge dt wedge dA wedge db.
```

The weight twenty-five uses `Y0=t^5*A,Y1=t^3,Y2=t^3*b` and the exact
three-Y Jacobian `3*t^10`. In particular one must not substitute the
formula for an X-independent numerator in this chart. All higher normal
jets contain the complete physical `M0` and `C0` above.

The unresolved constructive step is to extend an appropriate exceptional
two-form through the full `t` family with its moving X-normal equation,
then compute its actual Gysin coefficient on `X0^3*Y0^3`. A nonzero
exceptional H20 form alone does not supply that extension or coefficient.

## A useful exact global chart for the extension problem

The invariant `r=epsilon^2/a^3=Y1^5/Y0^3=1/A^3` eliminates the temporary
weighted cover. Put `C0=1+b^6+a^6`, `K=1-14*a^6+a^12`, and retain the
original `M0=mjk*b+a*(mij+mik*b)`. On the graph normalization the full
two equations become

```
16*M0 = r^2*C0*K,
16*HX = -r^3*a^3*C0*(1+a^6)^2.
```

These follow exactly from the strict graph equation and the original
sextic. They retain all normal jets and exhibit the exceptional surface
at `a=0`. The tentative global two-form is simply

```
gamma_tentative = r*dx wedge db/z^3.
```

It has the correct exceptional restriction but is not known to be
closed; `r,z` both vary with `a` through the two equations. This chart
is a concrete full-source starting point for finding a closed extension.
Adjoining independent constant Fermat roots would trivially extend the
form on a new cover, but its trace can vanish; such an adjunction is not
a descent argument.

On the further open set `a*M0*(1+a^6)!=0`, the two equations also give

```
r=-HX*K/[a^3*M0*(1+a^6)^2],
HX^2*C0*K^3=16*a^6*M0^3*(1+a^6)^4.
```

This retains the full mixed coefficient. For fixed direction `(a,b)` it
is a plane torus-curve equation of the form `sextic^2=constant*quartic^3`;
it is not an isotrivial product presentation of the full graph.

## Four invariant exceptional holomorphic two-forms

The full candidate space is small enough to retain rather than choosing
only `gamma`. On `Cprime` the anti-invariant holomorphic one-forms have
the basis

```
xi^(i-1) dxi/z^j, i odd, 1<=j<=5, 1<=i<2*j.
```

There are fifteen. On `G` the three holomorphic one-forms are
`b^l db/y`, `l=0,1,2`. Simultaneous sign quotient leaves their entire
forty-five-dimensional tensor product in exceptional H20. For the
original order-six generator, tensor invariance requires
`i=2*l+1 mod12`; the order-three generator requires `i-2*j=0 mod3`.
Exactly four triples survive:

| i | j | l | rational two-form, up to nonzero constants |
|---|---|---|---|
| 1 | 2 | 0 | `r dx db/(x*b*z^2)` |
| 1 | 5 | 0 | `r dx db/(x*b*z^5)` |
| 3 | 3 | 1 | `r dx db/z^3` |
| 5 | 4 | 2 | `r*x*b dx db/z^4` |

This is a four-dimensional exceptional source-character space, not a
four-dimensional class space already present on the full graph
normalization. A possible global extension must consider compatible
linear combinations.

For the third tentative form, differentiating the exact global chart
at `a=0`, with `x,b` fixed, gives

```
z_a=0, r_a/r=(z^3/2+z^2*x*b/3)/(x*b),
partial_a gamma = r*(1/(2*x*b)+1/(3*z))*dx db.
```

The first summand is the exact form `d(4 db/w)` on the exceptional
surface. The second is `(4/3)*(xi dx/z) wedge (b db/y)` upstairs and
remains in the naive lift. Thus the visible elliptic product form does
not automatically give a closed lift. This derivative is not by itself
declared an intrinsic Kodaira--Spencer obstruction: a legitimate
holomorphic extension of the relative form, including moving pole and
normal corrections, must first be supplied.

Prepared with OpenAI Codex assistance.
