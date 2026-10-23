# Frozen constructive current handoff, 2026-10-23

The user stopped new research and requested a GitHub handoff. This file freezes
the latest local calculation. It is **not** a source primitive or a certificate.
No external write was made by this agent.

## Exact source and previously verified current

Use the full compact eight-component connection and fiber primitives in
`../ruling-source/full-base-connection/`. Coordinates are physical `(i,j,w)`;
native connections use `(i,j,v)`, so all physical `v_j,v_w` chain terms are kept.

Set

```
T=1+w^3
N=9*i^2*w^2-16*j^2*T
L=256*T^5*N+729*i^6*j^2*w^6
v=64*j^2*w*N*T^2/(9*i^2*L)
A=9*i^3*w*T/(j^2*N)
S=A*Q,  Q=(4-Gamma_D)*e6
```

Here `e7=e_bq` is the last compact basis vector (zero-based index 7).
Theta independently verified the combined N and j=0 current

```
c0=-i*T/(4*w*j)+28*T^2*j/(45*i*w^3)
Pj=c0*e7, Pw=Pi=0
```

in `../theta-compact/actual-N-j-removed-source-results.json` (22 exact groups).
That file contains the actual full source-bound vectors, with common curve
denominator Dcurve:

```
B=(Q+GammaV*e7/30)/v
H=(GammaV*e7-5*e7)/v
J=(Gamma_j*e7)/v.
```

All three are regular at v=0. No compact component may be discarded. Generic
identity and literal fiber-current references remain those in Theta's file.

## Latest joint w/j current

An elementary exact vector field preserves the already served divisors:

```
Vj=j*(2-w^3)/(2*i*w^3)
Vw=T/(i*w^2)
V(N)=Vj*N_j+Vw*N_w=2*T*N/(i*w^3).
```

Set `D0=-448/405` and add `D0*(Vj*e7,Vw*e7)` to the j/w current:

```
c=c0-224*j*(2-w^3)/(405*i*w^3)
d=-448*T/(405*i*w^2)
Pj=c*e7, Pw=d*e7, Pi=0.
```

This creates no N pole because V is logarithmic along N; it has no j=0
denominator beyond the original c0 term, and creates no T=0 pole because Vw
vanishes on T and Vj has no T denominator.

The exact retained compact residual is

```
R=S-div_connection(P)
 = A*v*B-c*v*J-lambda*v*H+r*e7

lambda=lambda0-(c*L_j+d*L_w)/(6*L)
lambda0=(-243*i^2*w^5-243*i^2*w^2
         +2016*j^2*w^6-3136*j^2*w^3-2464*j^2)
        /(4860*i*j^2*w^3)
r=-28*(117*w^6-110*w^3-35)/(1215*i*w^3)
  +5*(c*L_j+d*L_w)/(6*L).
```

This follows by differentiating c,d and using the exact B/H/J definitions:

```
lambda=(c*v_j+d*v_w)/(6*v)+A/30
r=-c_j-d_w-5*lambda.
```

The elementary identities for V(N), lambda0, and r were checked with SymPy.
The large eight-vector identity has **not** been independently rerun after
this latest w/j addition. It follows formally from the already checked generic
connection and B/H/J identities, but this scope must remain explicit.

## Boundary effect and remaining work

The earlier current's w=0 residual has leading
`-224/(135*i*w^3)*e7`. The new V current has leading
`3*D0/(2*i*w^3)*e7`, so it removes that pole of order three. The local
calculation uses

```
v=j^2*w/(36*i^2)+O(w^4)
GammaV(0)*e7=5*e7
Gamma_j(0)*e7=0.
```

In the displayed r expression its order-three coefficient cancels explicitly:
the first term contributes `196/(243*i)`, the L derivative term contributes
`-196/(243*i)`. The remaining B/H/J terms have at most order two at w=0.
Its explicit denominator scope remains only i,w,L,Dcurve, with no N,j,or
fold denominator; factors j in c are absorbed by v and by L_j.

**Still open:** the lower w=0 jets, the i=0 profile, the Dcurve/lognormal
residue correction, and the full compact source primitive. No further solve
was launched after the stop instruction.

For a future constructive continuation one can use exact finite local
Hermite reduction with the full eight-component connection; the generic
GammaV0 spectrum is {1,2,4,5}, each twice. The physical w residue is
GammaV0/6. A naive w-only current reintroduces N poles, so use joint currents
or retain every boundary correction explicitly.

Fresh additionally has a polynomial compact Wbq with native
`nabla_j|v Wbq=e7` in
`../ruling-source/full-base-connection/j-source-primitive-results.json`
(33 exact groups), including its literal fiber primitive. Weighted uses must
retain density derivatives and the physical v_j*Gamma_v*Wbq term.

## Earlier work retained with its actual scope

`quartic-w-connection-results.json` contains the exact rank-three trace-free
quartic algebra connection; it does not integrate the original source.
`complete-rr-modular-source-results.json` is restricted relative-w feedback,
not a global obstruction; its actual-H evaluator audit was pending when
parent directed no further w-only solves. `i-j-moment-current-results.json`
contains exact alternative i/j moment identities; the i primitive retains a
finite third-kind companion and cannot be treated as pure compact.

Original source binding and all second-kind, infinity, finite, physical-cover,
and fiber-exact components remain mandatory. No certificate, Lean proof,
kernel verification, protected CI, solve PR, or acceptance has been produced.
