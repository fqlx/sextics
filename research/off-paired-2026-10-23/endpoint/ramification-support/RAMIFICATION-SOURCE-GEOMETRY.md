# Actual normalization ramification and a mixed-source obligation

No primitive, target Gysin match or certificate is known. This records a
distinct support, its complete cube-root character, explicit holomorphic
two-forms and the limitation of using only forms from the base surface.

## A genuinely different degree-eighteen support

Write `w=X0,x=X1,u0=X2,y=Y0,z0=Y1,v0=Y2`. The homogenization of the
normalization branch is

```
Ddelta=3u0^6 v0^6 z0^6-3u0^6 v0^6 w^6
       -8u0^6 y^6 z0^6+u0^6 y^6 w^6
       -x^6 v0^6 z0^6+2x^6 v0^6 w^6.
```

It is not one of the six earlier CM graph supports, including after
restriction to the physical fourfold. For example, take `w=z0=0` and
the sixth powers `(x^6,u0^6,y^6,v0^6)=(1,3,2,-6)`. Then `F=Ddelta=0`,
while the old X supports have values `(128,-36,-4)` and the old Y
supports have values `(-144,-832,-16)`. Thus the earlier fixed-support
calculations do not test this divisor.

## Keep the actual cyclic cover

Use the canonical-family parameters `r,s,k,z`, where

```
R=r^2, S=s^2, k^3=rs,
Delta=3RS z^6-3RS-8R z^6+R-S z^6+2S,
mu=dr dk dz/(9r)=dr ds dz/(27k^2).
```

Set `u=1/r,v=1/s,h=1/k` and abbreviate

```
P=2-z^6, Q=1-8z^6, T=3(z^6-1),
uv=h^3,
Qcrit=P u^2+Q v^2+T,
Wcrit=P u^2-Q v^2.
```

Then `Delta=h^-6 Qcrit`. The actual ramification surface is
`uv=h^3,Qcrit=0`, rather than the rational conic obtained by dropping h.
Its genus-two quotient satisfies

```
Wcrit^2=T^2-4PQ h^6.
```

On a common finite root cover of the z-line choose

```
alpha^2=P/T, beta^2=Q/T, gamma^3=alpha beta.
```

This cover has degree at most twelve. Put

```
a=alpha u, b=beta v, ell=gamma h.
```

The surface is dominated by the product of this explicit base curve
with the fixed genus-four curve

```
C0: ab=ell^3, a^2+b^2+1=0.
```

This statement includes all function-field generators. It does not
identify the actual moving canonical curve fiber with C0. The latter
is the curve parameterized by `(r,k,z)` in the original fibration.

## Explicit invariant holomorphic two-forms

Let `W0=a^2-b^2=Wcrit/T`. The four canonical differentials

```
dell/W0, ell dell/W0, a dell/W0, b dell/W0
```

are holomorphic on C0. The rational forms on the actual surface

```
sigma_f=f dh wedge dz/Wcrit, f in {1,h,u,v}
```

pull back to the above four differentials wedged, respectively, with

```
dz/(T gamma), dz/(T gamma^2),
dz/(T alpha gamma), dz/(T beta gamma).
```

All four base differentials are holomorphic. At each of the six roots
of P, Q or T the full root cover has ramification index six. In the
listed order their vanishing orders are

| Place | Four orders |
| --- | --- |
| P=0 | 4,3,1,4 |
| Q=0 | 4,3,4,1 |
| T=0 | 1,3,4,4 |
| z=infinity | 4,4,4,4 |

They have no other poles. Hence `z^i sigma_f`, `0<=i<=4`, give twenty
linearly independent holomorphic two-forms on a resolution of the
actual ramification surface. Descent is explicit: a deck action
`(alpha,beta,gamma)->(ea alpha,eb beta,eg gamma)`, with
`ea^2=eb^2=1,eg^3=ea eb`, acts on `(a,b,ell)` by the same factors.
The curve differential and its corresponding base differential have
inverse characters. Their product is the displayed rational sigma_f.

For the source character, `k->zeta3 k` gives `h->zeta3^-1 h`.
The form `sigma_h` has character `zeta3^-2`, exactly the character of
the physical density `mu`. This character match alone is not a Gysin
source match.

There is also a literal elliptic-surface quotient:

```
xE=-4PQ h^2, yE=-4PQ Wcrit,
yE^2=xE^3+16(PQT)^2,
dxE/yE=2h dh/Wcrit   (relative to z).
```

Thus the five forms `z^i sigma_h` are pullbacks of holomorphic forms
on a j=0 elliptic surface of Euler characteristic six. Equivalently,
put `delta=T gamma^2`, so

```
delta^3=PQT=3(z^6-1)(2-z^6)(1-8z^6).
```

This cubic cover has genus sixteen and `dz/delta` is holomorphic.
The z coordinate is retained; replacing it by `Z=z^6` loses its deck
character and changes the differential.

## Exact normal residue and the apparent density pole

With residue orientation `dQcrit` first, followed by `dh wedge dz`,

```
Res(mu/Delta)=h^4 dh wedge dz/(18Wcrit),
k^3 Res(mu/Delta)=sigma_h/18.
```

This calibrates the scalar and orientation of the useful holomorphic
candidate. The unweighted density residue is a different meromorphic
form; multiplication by k cubed is not licensed by the immutable target
without a corresponding current/source identity.

The normalized-moduli formula

```
source=-H partial_e(eta'_b) dc dd de,
H=4(1+z^6)^(4/3)(1+R)^(11/6)(1+S)^(5/6)/(z k Delta)
```

does not itself give a pole of the full source on this surface. The
Jacobian `dc dd de` has a compensating Delta zero. On the open where
the other factors and the canonical curve are smooth, the complete
physical source is regular at Delta, so its direct Poincare residue
there is zero. The map has a genuine simple fold: at `(R,S,z)=(1,7,1)`
the kernel of its logarithmic Jacobian is `(2,-56,1)`, whose derivative
of Delta is `-34`. Any nonzero serving residue must therefore come
from an actual transgression current, not the scalar H pole alone.

## Why a mixed class is still required

The above twenty forms come from the ramification **base** surface.
Let a resolved proper curve fibration be `pi:Xtilde->Btilde`, with
Btilde a rational compactification of `(r,k,z)`, and let the divisor
over the branch surface S be D. On the transverse smooth part, the
projection formula gives

```
iD_* piD^*(alpha)=pi^* iS_*(alpha).
```

The pure-base term on the right has no `(3,1)` component because
`H^(3,1)(Btilde)=0`. Resolutions and boundary components must be
tracked when using this identity globally; it does not exclude every
class on D. It does show that pulling back the displayed holomorphic
base forms supplies no target class by itself.

The constructive obligation is a closed mixed form on the actual D,
with a canonical-curve differential wedged with a base differential,
or a complete normal-function transgression whose exceptional/boundary
terms carry that mixed class. In relative de Rham notation this means
finding a closed one-form on S with values in the actual rank-eight
curve module, with its Hodge and rationality conditions satisfied.
No such mixed form, fixed elliptic subfactor of the moving curve or
source-compatible Gysin identity has been found here.

`verify_ramification_geometry.py` checks the support distinction,
toric branch equation, density and residue constants, actual elliptic
quotient, complete density cancellation and the stated holomorphy
orders. It performs no denominator search.
