# Physical D32 conductor/Fermat corner

This packet derives a genuine local normalization model for the physical
effective-graph divisor. It does not identify a global serving class or a
rational-vector-field certificate.

The input is the literal primitive degree32 polynomial in
`/workspace/research/round9/abel_prym/effective_graph.pickle`. Its 558 terms have
X-total degrees17 and19 and are independent of X2. The initial X-degree17
part has310 terms. The original variable order is
`(X0,X1,X2,Y0,Y1,Y2)`.

## Coordinates and exact initial equations

Work on Y2=1, at one of the six points
`X0=X1=X2=Y1=0, Y0=zeta, zeta^6=-1`. Put

```
X0=eps, X1=v*eps, X2=W, Y1=b,
delta=Y0^6+1, delta=b*r,
Y0=zeta*(1-delta)^(1/6).
```

The five coefficients A,B,C,D,E are in `blowup_quadratic.json`. With weights
`(eps,W,b,r)=(3,2,6,6)`, the actual two equations have initial forms

```
F0 = W^6+b*(r+(5/7)*zeta*eps^2),
D0 = A*r^2+C*b*r+D*b^2+eps^2*(B*r+E*b).
```

Both have degree12. The second equation is the strict transform obtained
after division of D32 by `eps^17*b^2`. All lower-weight terms vanish.
`weighted_ci_audit.py` derives this directly from the original D32 and checks
every coefficient against the five-coefficient packet. In particular the
packet uses **delta=Y0^6+1**, rather than Y0-zeta: the raw coefficient of
`(Y0-zeta)^2` is A*(6*zeta^5)^2.

The finite-prime check p101,zeta10,v2 gives

```
F0=W^6+b*(r+36*eps^2),
D0=57*r^2+57*b*r+59*b^2+eps^2*(55*r+3*b).
```

The ideal of both equations and all two-by-two Jacobian minors has
dimension0 and colength83. `ci_p101_z10_v2.sing/log` records this complete
quasismoothness check. Independently,
`/workspace/research/round9/abel_prym/corner_CI_audit.py/json` proves an exact
quasismooth witness at v2 over both cyclotomic components of zeta^6+1.

## Why this is a normalization chart

Write S=Y0^6+Y2^6 and beta=Y1. The original D has an exact decomposition

```
D=q*S^2+beta*rho*S+beta^2*sigma,
deg(q,rho,sigma)=(20,25,30).
```

The integral generator theta=q*S/beta satisfies

```
theta^2+rho*theta+q*sigma=0,
beta*theta=q*S,
S*theta=-rho*S-beta*sigma.
```

The corresponding global intermediate finite algebra is recorded by the
rank-candidates agent in `/workspace/research/round10/conductor_collision`.
All three coefficients have X-total degree at least17. Consequently, after
the first `(X0,X1)` blowup, theta/eps^17 is integral. At the corner its
coefficient q/eps^17 is the unit A(v) for generic v. Thus
`r=S/beta=(theta/eps^17)/(q/eps^17)` is integral there. The chart above is
finite over the first strict transform. Its isolated transverse ICIS is
normal, so it is the local normalization, rather than merely a blowup of a
singular center.

## Local adjoint defect and characters

For the weight(3,2,6,6) blowup the transverse surface discrepancy is

```
(3+2+6+6)-1-(12+12)=-8.
```

Quasismoothness makes the strict transform smooth on the stack; its coarse
quotient singularities are rational. The local adjoint condition is
weight(f)>=8. Higher-weight terms in the actual equations do not change
this condition, since their restrictions to the exceptional curve vanish.
The ten surviving low-weight monomials are

```
1, W, eps, W^2, eps*W, W^3, eps^2, b, r, eps*W^2.
```

The generic transverse geometric genus is therefore10. Under W->omega*W,
the residue dualizing generator has character1, so a monomial with W
exponent j has dualizing character j+1 and H1(O_resolution) character
`-j-1 mod3`. The three H1(O) multiplicities are `(2,2,6)`.

The six character2 layers correspond to dual adjoint monomials
`1,eps,eps^2,b,r,W^3`. The additional global Y-sign involution sends eps,W
to their negatives and leaves the total CI canonical frame invariant.
Its even part retains precisely `1,eps^2,b,r`.

This is a local result. The coherent extension along the full v-line and
the global adjoint map remain separate. In particular the generic model
degenerates at v=infinity and at zeros of its explicit discriminants.

## Source and global limitations

The independently audited actual source pullback in this chart is

```
-eps^4*b/(6*Y0^2) *
d eps ^ dW ^ db ^ dr ^ dv / F^2.
```

In the infinity chart u=1/v, eps'=X1, it becomes

```
+u^3*eps'^4*b/(6*Y0^2) *
d eps' ^ dW ^ db ^ dr ^ du / F^2.
```

The generic total canonical CI frame transforms by
`Omega'= -v^16*Omega`; multiplying its slot by eps^i gives exponent16+i.
These are generic patch transitions, not a completed global vector-bundle
splitting. The source's pulled-back pole-two numerator is not, by itself,
the canonical adjoint-defect representative; no source projection is
claimed from its weight alone.

Generic ordinary conductor contributions have a separate exact coherent
description and global canonical restriction is surjective there. The
weighted corner calculation above concerns the additional normal
singularities after finite normalization. To conclude H20 or construct a
certificate still requires the global connecting map and the actual
Gysin/source calculation.

Reproduce: run `weighted_ci_audit.py`; then run the independent
`corner_CI_audit.py` cited above.

## The actual X0=0 collision away the vertices

`infinity_line_audit.py/json` treats the distinct open chart

```
Y2=1, X1=tau!=0, X0=u*tau, delta=Y0^6+1=b*r.
```

Along u=b=r=0 one has X2^6+tau^6=0, so X2 is eliminated etale. Moreover
`q=-533655864*zeta*tau^19` at this locus; hence r is an actual finite
normalization coordinate. The normalized transverse equation
`D/(tau^17*b^2)` has a unit r^2 coefficient. Its three Newton faces are

```
(wt(u),wt(b),wt(r))=(3,2,6), degree12:
 -147*(-13125*b^3*r*zeta^5+6250*b^3*tau^2*u^2
       +3630312*r^2*tau^2*zeta);

(1,2,4), degree8:
 -294*tau^2*(3125*b^3*u^2+52500*b^2*u^4*zeta^5
            -196000*b*u^6*zeta^4+1815156*r^2*zeta);

(1,8,7), degree14:
 -57624*tau^2*zeta*(-1000*b*u^6*zeta^3
                   +9261*r^2+3150*r*u^7*zeta).
```

All cubic and higher r terms lie above these faces. Completing the unit
r^2 term gives a double cover with branch Newton vertices
`(0,6),(2,3),(6,1),(14,0)`. The outer edges are binomials with nonzero
coefficients; the middle edge quadratic has discriminant
`-26471025000000*zeta^4`, nonzero on both cyclotomic components. Thus this
is Newton nondegenerate for every tau!=0.

For the canonical double-cover form du^db/y the three adjoint thresholds
are respectively2,2,-1. The resulting adjoint ideal in the normalized
surface is `(u^2,b,r)`, with quotient basis `1,u` and transverse geometric
genus2. This formula is local along the36 lines

```
X0=Y1=0, Y0=zeta*Y2, X2=eta*X1,
zeta^6=eta^6=-1.
```

The two endpoints tau=0 and Y2=0 require separate models. This computation
does not decide the coherent extension along the complete lines or their
global source image.

For a global canonical numerator P=Y1*G31+S6*H26 already in the ordinary
conductor ideal, this new local condition is G31 in `(X0^2,Y1,S6)`.
Equivalently, away the endpoints, P lies in
`(S6,Y1^2,Y1*X0^2)`. The new defect module is the corresponding quotient
`O_T(-1)`, where `T=(Y1,S6,X0^2) intersect X` is a CI(1,6,2). Its
interaction with the Fermat-center adjoint condition cannot be omitted.

## Higher vertex valuation at infinity

The exact full Newton calculation in
`/workspace/research/round11/d32_corner_elliptic/vertex_newton.py/json`
finds the further vertex valuation

```
wt(X0,X1,X2,Y1)=(7,5,5,16), wt(delta)=30,
ord(F)=30, ord(D)=155.
```

The initial D has the factor X1^12 and residual weighted degree95. The
residual main surface is rational: put

```
v=X2/X1, z=X0^2*Y1/X1^6, h=X0^5/X1^7,
d=-1-v^6-(5*zeta/7)*z.
h=(3150*zeta^2*z^2*d+1000*zeta^3*z^3-9261*d^2)
  /(6615*d^2+3150*zeta*z*d).
```

The exponent lattice generated by z,h is saturated because the cross
product of `(2,-6,1)` and `(5,-7,0)` is exactly `(7,5,16)`. Thus the
display is birational, not merely a finite parameter cover.

This rational main component still imposes a strong adjoint condition.
The ambient fourfold X is smooth at the vertex. Its weighted discrepancy
is32 and D has order155, so a canonical numerator P must have
`wt(P|X)>=123` along the main multiplicity-one component. Here P|X uses
the equation F to eliminate delta; an unexpanded raw Y0 monomial does not
give the correct valuation. This is a necessary extension condition, not
a calculation of the entire global adjoint ideal. The main component and
the reduced intersection curves are rational; multiplicities, normal
layers, and further singularities remain separate.
