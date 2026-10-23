# Independent companion toric audit

The current companion formulas pass the independent audit. The audit found
no additional error. It confirms the nonzero infinity correction already
present in `coupled-fresh/infinity-horizontal/COMPANION-TORIC-CROSS.md`.
No primitive or certificate follows from this audit.

## Method and scope

`verify_companion_independent.py` uses Python `Fraction` arithmetic and
fresh truncated Newton solutions of the implicit quartic. It imports no
primary derivative, connection, Cartan, or polynomial-reduction routine.
The primary polynomial/J expression is read only as an expression to be
evaluated against an independently computed differential.

All 85 checks pass:

- Eight fresh normalized rational curve points test all four literal cross
  rows against q-derivatives of their rational fiber primitives, and both
  companion self-operator currents: 48 checks.
- Six universal rational points test the direct B source, its E derivative,
  and the corrected polynomial/J compact representative: 18 checks.
- Two independent Pb branch Taylor solutions test the finite residue and
  cancellation of the third-, second-, and first-order principal parts:
  eight checks.
- The Pa valuation verifies regularity of the exact potential: one check.
- Two independent projective infinity branches test the nonzero xi residue,
  the normalization shift, the corrected compact residue, regularity of
  xi2, and the retained fifth-order compact pole: ten checks.

These fresh-point checks support the primary generic symbolic identities;
they are not a substitute for a universal coefficient proof. The following
formal calculations independently explain the source and residue constants.

## Literal source and finite poles

Write

```
ab=q³, Q=Aa²+Bb²+Cq²+Daq+Eq+T,
J=aQ_a−bQ_b, eta_b=b dq/J,
xi=a dq/q, xi2=dq/b.
```

At fixed q, differentiating the norm and quadric equations with respect to
B gives `b a_B+a b_B=0` and `Q_a a_B+Q_b b_B=−b²`.
Solving gives `b_B=b³/J`. Therefore

```
partial_B xi2=−eta_b,
partial_E partial_B xi2=−partial_E eta_b=tau.
```

This is the actual source identity, including its sign. It does not assert
that the coefficient direction can be integrated on the actual base without
the base/tori lift and its adjoint corrections.

At Pb, take `a_s²=−T/A`, `b=q³/a`, and solve the quadric through degree two:

```
a=a_s+a1 q+a2 q²+O(q³),
a1=−D/(2A)−E/(2A a_s),
a2=r a_s,
r=[C−D²/(4A)−E²/(4T)]/(2T).
```

Since `xi2=a dq/q³`, its residue is `r a_s`. The exact potential

```
F_b=a/(2q²)+(D a²+E a)/(4Tq)
```

cancels the third- and second-order poles. At Pa, `a=O(q³)` makes all
terms of this potential regular. Subtracting `r xi` cancels the remaining
finite residues.

## The mandatory infinity term

In the projective chart `a=1,q=u,t=u³/b(u)`, let `b(0)=c0`,
`c0²=−A/B`. The quadric implies

```
b(u)²=−A/B−Du/B−Cu²/B+O(u⁴).
```

However

```
xi=[b'/u³−2b/u⁴]du,
res xi=[u³]b(u)=D(C−D²/(4A))/(4ABc0).
```

The vanishing cubic coefficient of b² does not kill that of b. Thus the
companion xi has opposite nonzero infinity residues in general. For
`omega=q²dq/J`, its residue is `−c0/(2A)`, and

```
s=D(C−D²/(4A))/(2A),
res(s omega)=res xi.
```

Consequently the corrected compact form is precisely

```
psi_hat=xi2+d_q F_b−r xi+r s omega.
```

Its infinity residues vanish. The raw expression without `r s omega`
has residue `−r res xi` and is not a compact de Rham input. The derivative
of `D a²/(4Tq)` retains a fifth-order infinity pole with leading coefficient
`−D c0/T`; this is second-kind data, not a removable residue claim.

## Cross rows and their actual fiber primitives

Normalize `A=B=T=1` and set

```
Q=a²+b²+cq²+daq+eq+1, J=2a²+daq−2b²,
A0=−c partial_c/3−2d partial_d/3−e partial_e/6,
B0=−c partial_c/3−d partial_d/6−e partial_e/6,
T0=−c partial_c/3−d partial_d/6−2e partial_e/3.
```

The literal normalized rows verified at every fresh point are

```
partial_c² zeta+(B0−1/6)partial_e xi=d_q f_BE,
partial_c partial_e zeta+B0(T0+1/2)xi=d_q f_BT,
(A0−1/6)partial_e zeta+partial_c² xi=d_q f_AE,
A0(T0+1/2)zeta+partial_c partial_e xi=d_q f_AT,

f_BE=aq/(6J),
f_BT=a(2cq²+daq+eq+3)/(18J),
f_AE=−bq/(6J),
f_AT=−b(2cq²+4daq+eq+3)/(18J).
```

The coefficient in the last numerator is **4d**, as in the corrected
primary record. The two self currents also pass:

```
[partial_e²−(T0+1/6)partial_c]xi=d_q[aq²/(3J)],
[partial_d²−(A0−5/6)partial_c]xi=d_q[−aq²/(6J)].
```

The source adjoint still has to close. If raw xi is replaced by its
zero-residue form `xi_hat=xi−s omega`, every full operator must act on
`xi_hat+s omega`. The audit does not authorize discarding that companion
before adjunction or concluding that its finite point pair is torsion.
