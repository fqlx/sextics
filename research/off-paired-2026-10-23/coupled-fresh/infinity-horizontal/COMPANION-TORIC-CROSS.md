# Companion toric pair with a literal eta_b source

Status: exact cross-source decomposition, with all infinity terms retained.
No primitive or certificate.

Use the universal family and orientation of `TORIC-POINT-PAIR.md`:
`ab=q³`, `Q=Aa²+Bb²+Cq²+Daq+Eq+T`, `J=aQ_a−bQ_b`,
`eta_b=b dq/J`, `Cp=C−D²/(4A)`.

The companion Pb point pair has the rational differential

```
xi=a dq/q,
xi_E=−a dq/J,
xi_C=−a q dq/J,
xi_B=−q² eta_b.
```

Its normalization by `a0²=−T/A` has residues +1,−1 at
`Pb±=(a=±a0,b=0,q=0)` and is regular at `Pa±`.
Unlike `zeta=b dq/q`, xi generally has nonzero infinity residues.

## The necessary infinity correction

In the projective chart `a=1,q=u,t=u³/b(u)`,

```
xi=[b'/u³−2b/u⁴]du,
b(u)²=−A/B−(D/B)u−(C/B)u²+O(u⁴).
```

Thus missing `[u³]b²` does not imply missing `[u³]b`. With `c0²=−A/B`,

```
res_(+c0) xi=c_xi=D Cp/(4ABc0),
res_(−c0) xi=−c_xi.
```

This corrects the tempting but false symmetric zero-residue analogy.
For `omega=q²dq/J` and `omega_inf=−(2A/c0)omega`,

```
s=D Cp/(2A), c_xi omega_inf=s omega,
xi_hat=xi−s omega.
```

The corrected form has zero infinity residues, with fourth-order
second-kind poles still retained.

## A direct source from the companion pair

The fiber-shifted companion differential is

```
xi2=xi/q²=dq/b,
partial_B xi2=−eta_b,
tau=−partial_E eta_b=partial_E partial_B xi2.
```

These identities are literal at fixed physical q. The new generator
therefore carries the original source, rather than just a q-weighted
replacement. It is regular at infinity. Its poles at Pb± have order three,
with residues `r a_s`, where

```
r=(Cp−E²/(4T))/(2T), a_s=±sqrt(−T/A).
```

Set

```
F_b=a/(2q²)+(D a²+E a)/(4Tq),
psi_hat=xi2+d_q F_b−r xi+r s omega.
```

At Pa, `a=O(q³)` makes `F_b` regular. At Pb, its derivative cancels
the third- and second-order poles. The remaining simple residues are
cancelled by `r xi`; the required `r s omega` cancels infinity residues.
Consequently psi_hat is a compact second-kind differential with only
infinity poles, of order at most five. No intermediate finite or infinity
pole is silently discarded.

Since `r_B=s_B=0`, the complete cross-source identity is

```
partial_B psi_hat=(r q²−1)eta_b+d_q(partial_B F_b)
                  +r s partial_B omega.
```

`companion-toric-cross.json` includes an explicit polynomial/J
representative for psi_hat. The independent full RR8 implementation
has reduced this corrected input, with its exact primitive retained, in
`../genus4-gm-independent/cross-compact-source-reduction-results.json`.
The raw form without `r s omega` is not compact and must not be passed
to that reduction as a compact source.

## Coefficient-only cross rows

The following literal universal identities also follow from the norm
relation and the fixed-q derivative lifts:

```
partial_B partial_E xi+partial_C² zeta=0,
partial_B partial_T xi+partial_C partial_E zeta=0,
partial_A partial_E zeta+partial_C² xi=0,
partial_A partial_T zeta+partial_C partial_E xi=0.
```

For normalized coefficients `A=B=T=1`, let `A0,B0,T0` be the Euler
fields in `normalized-third-box.json`. The first two compact rows become

```
partial_c² zeta+(B0−1/6)partial_e xi=d_q f1,
partial_c partial_e zeta+B0(T0+1/2)xi=d_q f2,
f1=−i_(q partial_q)(partial_e xi)/6,
f2=−i_(q partial_q)[((T0+1/2)/6−B0/3)xi−Rq xi/18].
```

Here `Rq=Lie_(q partial_q)`. The symmetric rows exchange xi,zeta and
replace B0 by A0. Their Cartan potentials must remain in actual currents.
All four can be written without formal Cartan operators. For normalized
`Q=a²+b²+cq²+daq+eq+1` their rational fiber primitives are

```
f_BE=aq/(6J), f_AE=−bq/(6J),
f_BT=a(2cq²+daq+eq+3)/(18J),
f_AT=−b(2cq²+4daq+eq+3)/(18J).
```

`verify_normalized_toric_cross.py` checks all four literal normalized
row-minus-d_q-primitive identities on the generic norm/quadric curve.
It also checks the companion's normalized self-operator currents:

```
[partial_e²−(T0+1/6)partial_c]xi=d_q[aq²/(3J)],
[partial_d²−(A0−5/6)partial_c]xi=d_q[−aq²/(6J)].
```

In these coordinates `s=d(c−d²/4)/2`, so the first row with zero-residue
xi_hat is

```
partial_c² zeta+(B0−1/6)partial_e xi_hat
   +s(B0−2/3)partial_e omega=d_q f1.
```

For a scalar multiplier W the dc dd de adjoint coefficients are
`partial_c² W` on zeta, `R_b W` on xi_hat and `s R_b W` on omega, where
`R_b=partial_e(B0−1/2)`. Hence setting the raw xi coefficient to zero
closes both its finite-pair and infinity residue contributions together.
This supplies additional coupled current choices; it is not itself a
solution of the remaining source-adjoint equation.

`verify_companion_toric_cross.py` checks fifteen exact symbolic groups,
including the actual eta_b derivative, residue correction, finite jet
cancellations, and polynomial/J compact representative. An independent
audit has been requested.

## Literal current on the actual rational base

The B source direction also has a rational physical lift, with the same
norm-torus conventions as `actual_ruling_adjoints.py`. Write

```
A=1+R, B=1+S, T=1+z⁶, k⁶=RS,
t=6z⁶/T, ca=2−1/R−3/S, cz=−6+4/R+2/S,
ZB=−1/[S(ca t+cz)], alphaB=t ZB,
vB=3(alphaB−ZB)/2, uB=−ZB−vB/3,
VB_R=A(alphaB−2uB−2vB),
VB_S=B(alphaB+2uB−2vB)+1, VB_z=z ZB,
c2=uB−vB/3.
```

All six coefficient identities verify `VB Q+uB E1Q+vB E2Q−alphaB Q=b²`.
The complete literal connection, including its Cartan fiber derivative, is

```
nabla_VB xi2=nabla_B xi2+c2 xi2−(2vB/3)d_q(q/b).
```

For the existing outer-E lift VE and
`ME=div_mu(VE)+c_eta,E`, use relative-first orientation `dq wedge mu`.
The actual source has the explicit partial current

```
Jpartial=eta_b wedge i_VE(mu)+ME xi2 wedge i_VB(mu)+K mu,
K=−(2/3)[vE qb/J+ME vB q/b],
G2=div_mu(ME VB)+ME c2,
(-nabla_E eta_b) wedge mu=d_total Jpartial+G2 xi2 wedge mu.
```

The remaining xi2 term is retained; no vanishing of G2 is asserted.
Substitution of the compact/point-pair decomposition above carries this
same remaining source into the full compact connection and both residue
sections. No coefficient cover is needed for this partial actual current.

`verify_actual_companion_current.py` checks twelve exact groups: the six
physical coefficient equations and all literal torus/scaling/Cartan
identities used here. Data are in `actual-companion-current.json`.

The separate audit `../../audit/companion-toric/COMPANION-TORIC-AUDIT.md`
passes 85 fresh exact Fraction/Newton groups for the new companion source,
its finite and infinity corrections, compact polynomial representative,
four cross primitives, and two companion self currents. It distinguishes
fresh-point independent checks from the primary generic symbolic proof.
