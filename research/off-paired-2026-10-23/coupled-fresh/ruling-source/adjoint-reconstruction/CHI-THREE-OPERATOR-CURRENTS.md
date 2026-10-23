# Three full-direction source-current generators

This is an exact constructive current-generation mechanism.  It is not yet a
source solution.  The finite poles and fourth-order infinity second-kind poles
of chi remain present in every differential identity.

Put `b0²=−T/B` and `chi=b dq/(b0 q)` on the actual canonical genus-four curve.
The three universal box identities are literal rational identities:

```
(partial_D²−partial_A partial_C)chi=0,
[partial_E²−partial_T partial_C−partial_C/(2T)]chi=0,
[partial_A(partial_B−1/(2B))(partial_T+1/(2T))−partial_C³]chi=0.
```

For the last identity, `zeta=b0 chi=b dq/q` is a local algebraic-root
differential.  Its plane polynomial is

```
P(b)=B b^4+(Cq²+Eq+T)b²+Dq^4 b+Aq^6.
```

The equal-order coefficient products `P_D²=P_A P_C`, `P_E²=P_C P_T`, and
`P_A P_B P_T=P_C³` give the boxes by the exact local-root residue formula.
Thus no fiber pole or boundary term is dropped in passing to these boxes.

## Normalized operators with their rational fiber primitives

Use the actual normalized `(c,d,e)` and density `Hsrc` from
`../NORMALIZED-MODULI-DENSITY.md`.  Define

```
A0=−c/3 partial_c−2d/3 partial_d−e/6 partial_e,
B0=−c/3 partial_c−d/6 partial_d−e/6 partial_e,
T0=−c/3 partial_c−d/6 partial_d−2e/3 partial_e.

PE=partial_e²−(T0+1/6)partial_c,
PD=partial_d²−(A0−1/3)partial_c,
P3=A0(B0−1/2)(T0+1/2)−partial_c³.
```

These normalized operators have rational fiber corrections.  They are not
asserted to kill the literal normalized differential at fixed q.  Write
`Rq=Lie_(q partial_q)` on relative one-forms and `iRq=i_(q partial_q)`.
The coefficient normalization has `q_physical=gamma q`, where
`gamma=T^(1/3)(AB)^(-1/6)`. Consequently the three universal coefficient
directions become

```
partial_A -> (A0+Rq/6)/A,
partial_B -> (B0+Rq/6)/B,
partial_T -> (T0−Rq/3)/T.
```

Put `Aop=A0`, `Bop=B0−1/2`, `Top=T0+1/2`, and

```
U=(Aop+Bop)Top/6−Aop Bop/3,
V=Top/36−(Aop+Bop)/18.
```

Then the complete rational relations are

```
PE chi=d_q rE, rE=−iRq(partial_c chi)/3,
PD chi=d_q rD, rD= iRq(partial_c chi)/6,
P3 chi=d_q r3,
r3=−iRq[U chi+Rq V chi−Rq²chi/108].
```

All base coefficient derivatives and Rq commute in the normalized local
coordinate.  These primitives include the Cartan corrections from changing
fiber coordinate; omitting them would leave only cohomological identities.

## Full scalar source equation and literal reconstruction

With the standard normalized density `dc dd de`, the exact adjoints are

```
PE*=partial_e²−partial_c(T0−4/3),
PD*=partial_d²−partial_c(A0−5/6),
P3*=partial_c³−(A0−7/6)(B0−1/6)(T0−5/3).
```

In particular `P3*(1)=35/108`; no inverse of this differential operator is
assumed.  The actual source has coefficient `−b00 Hsrc partial_e²chi`, with
the fixed nonzero constant `b00²=−1`.  After absorbing b00 into currents, a
sufficient source-carrying equation for three arbitrary rational/algebraic
potentials is

```
PE* f+PD* g+P3* h=−partial_e² Hsrc.                 (1)
```

No finite-residue or infinity-residue equation has been suppressed: chi has
fixed finite residues and zero infinity residues, and its second-kind terms
are retained literally.  This is a broader current mechanism than the
single ruling-annihilator interpolation. It is not claimed complete for
arbitrary genus-four currents.

For exact reconstruction, let `B_P(w,chi)` be the base vector current obeying
`w Pchi−(P*w)chi=div B_P`.  Explicitly,

```
B_PE=(f chi_e−f_e chi)partial_e
     −f chi_c T0+(T0 f−4f/3)chi partial_c,
B_PD=(g chi_d−g_d chi)partial_d
     −g chi_c A0+(A0 g−5g/6)chi partial_c.
```

For P3 put `A*=−A0+7/6`, `B*=−B0+1/6`, and use

```
B_P3=h (Bop Top chi) A0+(A*h)(Top chi) B0+(B*A*h)chi T0
     −(h chi_cc−h_c chi_c+h_cc chi)partial_c.
```

If (1) is satisfied, the source is exactly the divergence of the base current

```
(−Hsrc chi_e+Hsrc_e chi)partial_e−B_PE−B_PD−B_P3
```

plus the rational fiber-exact term

```
d_q(f rE+g rD+h r3).
```

This is an explicit route from reviewable potentials to an actual rational
current.  No potentials solving (1) have yet been found.  The source density
and every physical Jacobian must remain in (1), and a candidate must be
substituted into the literal divergence identity before being called a solve.

`verify_chi_three_operators.py` checks the two quadratic normalized primitives
directly in the implicit function field, the complete cubic Cartan expansion,
all three box monomial equalities, and all three Green identities exactly.
