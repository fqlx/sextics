# Fresh portfolio pass: four-plus-two and an anti-sensitive trigonal correspondence

No certificate or easier complete route was found in this pass. All files here are outside the protected repository.

The current alternate-target exclusions and `ACTIVE.md` were read before this work. The previously screened low-degree denominators, fixed-CM routes, cyclic scalar route, short-power joins and eight-plane Euler supports were not repeated.

## Exact four-plus-two core and character

Use `(a,b,c,d)=(X0,X1,Y0,Y1)`. On the core cyclic triple cover `T^3=H(a,b,c,d)`, the involution `(a,b)->(-a,-b)` preserves the holomorphic three-form. The source numerator `a^3*c^3` changes sign. Its anti part has Hodge level one, but **level one alone does not prove geometric coniveau one**. No general theorem upgrading this particular involution sector was established.

Set `u=a/b`, `v=c/d`, `r=b/d`, and `t=5/7`. Then

```
H/d^6 = f(u)*r^6 + t*u^3*v*r^4 + 2*t*u*v^3*r^2 + g(v),
f(u)=u^6+t*u^5+2*t*u+1,
g(v)=v^6+t*v^5+3*t*v+1.
```

After a finite cube-root normalization the curve over `(u,v)` is

```
C: w^3=r^6+A*r^4+B*r^2+C0,
A=t*u^3*v/f(u), B=2*t*u*v^3/f(u), C0=g(v)/f(u).
```

The involution is `r->-r`. Its elliptic quotient is `w^3=s^3+A*s^2+B*s+C0`, `s=r^2`. The anti part is a three-dimensional Prym with order-three signature `(2,1)`. This recovers a Picard-type local system, rather than an immediate Fano companion.

## Explicit correspondence retaining the anti character

Write the normalized coefficients as `A,B,C0`. If `r1^2,r2^2,r3^2` are the three roots of `s^3+A*s^2+B*s+C0-w^3`, set `p=±r1±r2±r3`. The eight signed sums satisfy

```
D7: [(p^2+A)^2-4B]^2=64*p^2*(w^3-C0).
```

Generically `D7` has genus seven. The explicit incidence between `C` and `D7` is

```
4*p*r*(p^2-2*p*r+2*r^2+A)-[(p^2+A)^2-4B]=0.
```

`trigonal_resolvent.py` verifies over QQ that its resultant with the sextic equation in `r` is the cube of the displayed `D7` equation. It also verifies the signed-fiber incidence projector. If `M` is its six-by-eight incidence matrix, then

```
M*M^t = 2*(id-iota) + 2*(all-fiber trace).
```

The all-fiber trace factors through the `w` projective line and acts as zero on H1. Thus the correspondence followed by its transpose is `4*id` on the actual anti H1 local system. The product-of-three-signs character, which gives the norm elliptic curve `z^2=w^3-C0`, is killed. This is an algebraic, anti-sensitive projector onto the desired Prym part, not merely an invariant trace.

The simpler genus-three quotient sets `q=p^2`, then `x=1/q`, `Y=4*x*w`:

```
Y^3 = [1+2*A*x+(A^2-4*B)*x^2]^2+64*C0*x^3.
```

It is fixed by simultaneous sign reversal of all radicals and therefore loses the actual anti character. Its existence alone is not a Prym isogeny serving the target.

An alternative compact expression for `D7` is the complete intersection

```
z^2=w^3-C0,
p^4+2*A*p^2+A^2-4*B=8*p*z.
```

At a fixed core ratio `u`, homogenizing the remaining variables gives degrees `(6,4)` in weights `(1,1,1,2,3)` for `(p,v,d,w,z)`. Adjunction gives canonical weight two, and its anti canonical forms include `p*v` and `p*d`. Thus this model still has the relevant two anti holomorphic two-forms on a generic surface fiber; it has not supplied a rational/Fano contraction. The remaining requirement is a genuine support construction or a controlled geometric correspondence using this anti summand.

## Independent fixed-support audit

`audit_fermat_fixed.py/json` independently rebuilds every column in Rank's cyclic `D=X2^6+Y0^6+Y1^6+Y2^6` test from the direct E1/E2 product rules. It checks the full source-character projection, all twelve exact homogeneous kernels and modular ranks `1236/1237` for `1248` columns. This independently seals that literal support's exact characteristic-zero exclusion. It does not exclude other supports.
