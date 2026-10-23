# Source-carrying b³ moment and its exact compact correction

Status: generic exact identities, independently derived from the two primary
proposals. No existence of a source-matching K or full certificate follows.

Work on the normalized curve

```
ab=q³, Q=a²+b²+cq²+daq+eq+1=0,
J=2a²+daq−2b², zeta=b dq/q,
Theta=b³dq/(3q²), Cp=c−d²/4, omega=q²dq/J.
```

The universal coefficient identity is literally
`partial_E Theta=partial_B zeta`. The normalized version includes the
coordinate-change fiber current:

```
partial_e Theta=(B0−1/2)zeta+d_q(b/6),
B0=−c partial_c/3−d partial_d/6−e partial_e/6.
```

This therefore carries the actual `(B0−1/2)zeta` defect, rather than a
different source obtained by discarding the curve differential.

## Finite-pole correction and two exact representatives

At Pa±, `b=b0−e q/(2b0)+O(q²)`, `b0²=−1`. Theta has a double pole and
residue `−e b0/2`; the residue is cancelled by `(e/2)zeta`.
The exact potential

```
F=b³/(3q)
```

cancels the double pole. All terms are regular at Pb± because `b=q³/a`.
The resulting differential has the exact polynomial/J representative

```
Theta+(e/2)zeta+d_q F=Nroot dq/J,
Nroot=2c b³+4d b²q²+6bq⁴+eaq²+(ed/2)q³.
```

The lower potential `Flow=−b/(3q)` also cancels all finite poles. Its
numerator is

```
Nlow=−(aq+cb+dq²)J/3+(2e/3)aq²+(ed/2)q³+(ec/3)bq
     +((e²−2c)/3)b−(4d/3)q²−2aq.
```

These representatives differ by the displayed exact primitive:
`(Nroot−Nlow)dq/J=d_q(F−Flow)`.

## Infinity residue and its sign

In the chart `a_projective=1,q_projective=u,t=u³/b(u)`,

```
Theta=[b⁴b'/(3u⁷)−2b⁵/(3u⁸)]du,
res(Theta)=−[u⁷]b(u)⁵/5.
```

Put `h=1+du+cu²`, with `c0²=−1`. Through degree seven, the exact implicit
equation gives

```
b(u)⁵=c0 h^(5/2)+(5/2)e u⁴h−(5c0/2)u⁶sqrt(h)+O(u⁸).
[u⁷]h^(5/2)=−5d Cp³/32.
```

The e term has no degree-seven coefficient. The last term contributes
`−5c0 d/4`. Consequently

```
res_(+c0) Theta=c0 d(Cp³+8)/32,
kappa=d(Cp³+8)/16,
Omega_Theta=Theta+(e/2)zeta+d_qF+kappa omega.
```

Since `res_(+c0)omega=−c0/2`, the counterterm has a **plus** sign.
Omega_Theta has only infinity poles of order at most eight, with zero
residues. Its explicit compact numerator is `Nroot+kappa q²`.
An RR reduction must permit an exact primitive with infinity pole order
at least seven; a smaller primitive bound would not verify this source.

The compact derivative has the useful literal interface

```
nabla_e Omega_Theta=b(−2cq−da+2e)dq/(6J)
                   +kappa nabla_e omega+d_q(F_e+b/6).
```

## Actual transfer of a fully weighted defect

Use `mu=dc dd de`, relative-first orientation, and let L be the complete
scalar multiplier, including any density weight. No kernel assumption on L
is needed for the identity

```
L(B0−1/2)zeta wedge mu
 =d_total JTheta
  +[−L_e Omega_Theta+(e/2)L_e zeta+kappa L_e omega] wedge mu,

JTheta=−L Theta wedge i_(partial_e)(mu)−(Lb/6)mu+(L_e F)mu.
```

Thus the finite section, infinity section, and full compact correction are
all retained in the transferred source. If, for example, the actual
multiplier is `L=e^(−7)K`, its derivative includes
`L_e=e^(−7)K_e−7e^(−8)K`. Removing that density derivative would change
the source.

`verify_theta_compact_moment.py` passes fifteen exact symbolic groups,
including both polynomial representatives, the source and Cartan identities,
finite principal parts, independent infinity-coefficient calculation,
counterterm sign, and compact derivative interface.
The explicit source inputs are in `theta-compact-moment.json`.
