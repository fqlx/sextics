# Coupled source equation for the two toric Jacobian sections

Status: exact source-carrying mechanism; no complete potential or certificate.
This enlarges the scalar toric-section construction. It retains the infinity
residue of xi and every second-kind principal part.

Work in the normalized family

```
ab=q³,
Q=a²+b²+cq²+daq+eq+1=0,
J=2a²+daq−2b²,
zeta=b dq/q, xi=a dq/q, omega=q²dq/J,
u=c−d²/4, s=du/2, xi_hat=xi−s omega.
```

The physical source, with its actual density H, is exactly
`−H partial_e² zeta dc dd de`. Here zeta is the raw normalized form,
not divided by b0'=±i, so no additional b0' factor is needed.
Zeta has zero infinity residues; xi has infinity residues du/(4i).
Xi_hat removes these residues but retains its fourth-order infinity
second-kind terms. Its finite residues are unchanged.

For compact operator notation put C=partial_c,E=partial_e,D=partial_d,
and

```
A0=−cC/3−2dD/3−eE/6,
B0=−cC/3−dD/6−eE/6,
T0=−cC/3−dD/6−2eE/3.
```

Their divergences for dc dd de are respectively −7/6,−2/3,−7/6.
The letter D in these displayed operators is a derivative, not the
universal aq coefficient.

## Four coupled rows with literal fiber primitives

The coefficient-only universal identities are

```
partial_B partial_E xi+partial_C² zeta=0,
partial_B partial_T xi+partial_C partial_E zeta=0,
partial_A partial_E zeta+partial_C² xi=0,
partial_A partial_T zeta+partial_C partial_E xi=0.
```

After normalization the complete rows are

```
C² zeta+(B0−1/6)E xi=d_q f1,
CE zeta+B0(T0+1/2)xi=d_q f2,
(A0−1/6)E zeta+C²xi=d_q f3,
A0(T0+1/2)zeta+CE xi=d_q f4,

f1=aq/(6J),
f2=a(2cq²+daq+eq+3)/(18J),
f3=−bq/(6J),
f4=−b(2cq²+4daq+eq+3)/(18J).
```

These are the independently derived Cartan corrections supplied by the
infinity-horizontal agent. They retain the actual q-coordinate change.
Substitute xi=xi_hat+s omega in every full operator. In particular the
omega coefficient is an operator applied to s omega, not s times the
operator applied to omega.

## Scalar self rows

The three zeta adjoints are

```
P1*=E²−C(T0−4/3),
P2*=D²−C(A0−5/6),
P3*=C³−(A0−7/6)(B0−1/6)(T0−5/3).
```

The analogous raw-xi adjoints differ because its normalizer is
`(T/A)^(1/2)` rather than `(T/B)^(1/2)`:

```
Q1*=E²−C(T0−4/3),
Q2*=D²−C(A0−1/3),
Q3*=C³−(A0−2/3)(B0−2/3)(T0−5/3).
```

Their primal normalized rows are respectively
`E²−(T0+1/6)C`, `D²−(A0−5/6)C`, and
`(A0−1/2)B0(T0+1/2)−C³`. They have the same Cartan recipe as the
zeta rows: r1=−i_(q partial_q)(Cxi)/3, r2=i_(q partial_q)(Cxi)/6;
for the cubic row use Aop=A0−1/2,Bop=B0,Top=T0+1/2 in the cubic
primitive from `adjoint-reconstruction/CHI-THREE-OPERATOR-CURRENTS.md`.

## Full coupled-adjoint source equation

Let f1,f2,f3 be zeta self-row potentials, g1,g2,g3 xi self-row potentials,
and w1,w2,w3,w4 potentials for the four cross rows. These potential names
are independent of the fiber primitives above. A sufficient actual source
equation is the pair

```
sum_j Pj* fj
 +C²w1+CEw2+E(A0−1)w3
 +(T0−5/3)(A0−7/6)w4 = −H_ee,                  (Z)

sum_j Qj* gj
 +E(B0−1/2)w1+(T0−5/3)(B0−2/3)w2
 +C²w3+CEw4 = 0.                                (X)
```

The explicit infinity equation is exactly s times (X). This follows from
formal adjunction of every complete raw-xi operator:

```
[L o multiplication_by_s]*w=s L*w.
```

Thus satisfying (X) cancels xi_hat and its infinity companion together.
It does not permit omitting the companion before adjunction. Standard
Green currents for these rows, plus the displayed fiber primitives, then
give a literal current for the source. Rational/algebraic potentials must
still be verified in that current and descended to the immutable target.

## An exact closed cross family

For the first cross row its xi adjoint is

```
Rb W=E(B0−1/2)W=(B0−2/3)W_e.
```

Therefore

```
W=e^(−3)F(c/e²,d/e)+G(c,d)
```

is a residue-compatible two-function family. It contributes C²W to (Z)
and zero to (X) and its infinity equation. This is a new constructive
source image rather than an unconstrained extra scalar potential.
The simple two-row curl w1=(T0−1)Z,w2=−EZ closes (X) too, but contributes
only `−P1* C Z` to (Z), already in the scalar self-row image.

## Rational form of the actual source in the closed-cross invariants

Set

```
i=c/e², Jinv=(d/e)², w=z², T=1+w³,
k=3iw/(4T), A=k²T/Jinv, R=A−1, S=k⁶/R,
v=e⁶=w³/(64T⁴ A(1+S)),
h=3i w³/(32 Jinv T² Delta).
```

Then the actual density has the exact factorization `H=e^(−5)h`.
All of h and v are rational in i,Jinv,w. The normalized coordinate
derivative eE is the following rational derivation:

```
mathcalD=−2i partial_i−2Jinv partial_Jinv
 +[(6v+2i v_i+2Jinv v_Jinv)/v_w]partial_w.
```

It satisfies E(c)=E(d)=0,E(e)=1 after the common e factor is restored.
Thus the actual source forcing is

```
H_ee=e^(−7)(mathcalD−6)(mathcalD−5)h.
```

For the residue-compatible subclass W=e^(−3)F(i,Jinv), its source image
is exactly `C²W=e^(−7)F_ii`. This reduces the source-dependent closed
cross channel to a rational algebraic reduction in the physical parameter w,
with i,Jinv as invariants. It does not assert that the remaining rational
forcing is w-independent or that the original source has been solved.
