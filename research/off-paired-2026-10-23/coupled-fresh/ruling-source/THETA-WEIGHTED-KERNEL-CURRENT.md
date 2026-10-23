# The full weighted Theta transfer for the actual retained kernel

This is a literal current identity and a forced compact source. It is not a
certificate. The source-bound rational construction of K is specified in
`adjoint-reconstruction/N-ONLY-RATIONAL-LIFT.md`; its all-pole residue proof
establishes rational integrability without dropping the curve-valued kernel.

Use the normalized complete intersection

```
ab=q³, a²+b²+cq²+daq+eq+1=0,
J=2a²+daq−2b², zeta=b dq/q, omega=q²dq/J,
Cp=c−d²/4, kappa=d(Cp³+8)/16,
B0=−c partial_c/3−d partial_d/6−e partial_e/6.
```

The raw zeta convention is used here. Replacing zeta by chi=zeta/(±i)
rescales every relative form and every current by the same constant.

## A literal first-order contiguity

Set

```
Theta=b³dq/(3q²), F=b³/(3q).
```

In the six-coefficient family, `partial_E Theta=partial_B zeta` literally,
since `b_E=bq/J`. Normalizing the coefficient B includes its fiber-coordinate
Cartan correction and gives

```
partial_e Theta=(B0−1/2)zeta+d_q(b/6).
```

For any entire base coefficient L, the product rule therefore gives

```
L(B0−1/2)zeta
 =partial_e(L Theta)+d_q(−Lb/6+L_e F)
  −L_e Omega+(e/2)L_e zeta+kappa L_e omega,             (Theta)

Omega=Theta+(e/2)zeta+d_q F+kappa omega.
```

Every term is a literal rational relative form. Base divergences carry the
flat normalized volume `dc dd de`; the displayed d_q terms are the vertical
part of the total current. This scalar coefficient form fixes the signs
without choosing a convention for the order of exterior factors.

## The source compact form, including its infinity correction

The exact polynomial representative is

```
Omega=[2c b³+4d b²q²+6bq⁴+eaq²+(ed/2)q³+kappa q²]dq/J.
```

At the finite Pa points, Theta has a double pole and residue `−(e/2)` times
the residue of zeta. The exact term d_q F cancels the double pole and
`(e/2)zeta` cancels the simple residue. There are no Pb poles. At the two
infinity points, with `c0²=−1`,

```
Res Theta=c0 d(Cp³+8)/32,
Res omega=−c0/2.
```

Thus the **plus** kappa omega term removes both infinity residues. Omega
is compact in de Rham cohomology, with all higher second-kind poles retained.
It must be reduced in the complete rank-eight connection; it must not be
set to zero merely because its residues vanish.

A further exact interface, independently derived by the infinity agent, is

```
partial_e Omega
 =b(−2cq−da+2e)dq/(6J)+kappa partial_e omega
  +d_q(partial_e F+b/6).
```

Equivalently this supplies the augmented primal row

```
E Omega−kappa E omega−B0 zeta−(e/2)E zeta
 =d_q(EF+b/6).
```

For a potential W its complete adjoint coefficients are

```
Omega: −W_e,
omega: kappa W_e,
zeta: (B0−1/6)W+(e/2)W_e.
```

The constants use `div B0=−2/3` and the derivative of e/2. Taking W=L
serves the Omega and omega coefficients of (Remaining) but leaves the
zeta coefficient `(-B0+1/6)L`. For the actual L this equals
`e^−7(Z−1)K`, exactly the original scalar remainder. Thus this one row
alone cycles back to the same source. An independent rank-eight connection
relation, or an actual coupled-adjoint potential, is needed for closure;
the compact E-interface by itself is not a solve.

## A source-driven use of the second toric section

The coupled rows can carry the independent infinity coefficient, provided
their finite Pb coefficient is retained and transferred into the compact
connection. Put

```
s=d Cp/2, xi_hat=xi−s omega,
f=kappa/s=(Cp³+8)/(8Cp).
```

This is a rational construction on the generic chart `d Cp !=0`; the final
cleared identity would have to extend and descend as usual. Both f and s
are e-independent in the normalized coordinates, and

```
partial_e xi_hat=−a dq/J−s partial_e omega.
```

Let Zop and Xop denote the complete scalar adjoints in equations (Z),(X)
of `COUPLED-TORIC-ADJOINT.md`. The source-driven, inhomogeneous pair

```
Zop=(e/2)L_e,
Xop=f L_e                                                (Coupled-Theta)
```

has raw-xi infinity coefficient `s Xop=kappa L_e`, exactly the independent
infinity coefficient in (Remaining). Subtracting the corresponding full
coupled currents leaves

```
−L_e Omega−f L_e xi_hat.
```

The Pb term is not discarded: its coefficient is an entire e derivative.
The explicit current `−partial_e(f L xi_hat)` transfers it and leaves the
following genuinely compact rank-eight source:

```
Ccompact=−L_e Omega+f L partial_e xi_hat
        =−L_e Omega−f L a dq/J−kappa L partial_e omega.    (Compact-Theta)
```

Every finite and infinity residue in this expression is zero. All eight
compact components remain; zero residues do not establish compact
exactness. Equations (Coupled-Theta) and the rank-eight connection for
(Compact-Theta) are a concrete enlarged closure problem for the actual
coefficient L. This is not an assumption that those potentials exist.
It allows the coupled section to serve a specific source coefficient,
rather than adding unrelated trial multipliers.

## Restoring the actual density and source sign

The scalar rational lift uses the positive forcing

```
Ssrc=(D−6)(D−5)h,
Ssrc−PE(Fpot)−PD(Gpot)−P3(Hpot)=(Z−1)K.
```

For `H=e^−5 h`, the actual source is `−H zeta_ee`; integrating twice in e
leaves the coefficient `−H_ee zeta`. Therefore its reconstruction uses the
negative of the displayed positive scalar lift, unless K and every potential
are negated consistently. The current (Theta) is stated for an arbitrary
positive coefficient L so this overall source sign remains explicit.

For the positive scalar-lift defect, the literal transfer is

```
e^−7(Z−1)K zeta
 =div(e^−7 K zeta Z)+L(B0−1/2)zeta,
L=e^−7 K,
L_e=e^−8(D−7)K.
```

Consequently its remaining curve-valued source, after the explicit Theta
current, is exactly

```
−e^−8(D−7)K Omega
 +(e/2)e^−8(D−7)K zeta
 +kappa e^−8(D−7)K omega.                            (Remaining)
```

Dropping the derivative of e^−7 would change all three coefficients.
Serving only the compact term would also leave the displayed finite and
infinity normal functions unmatched.

## The integration constant is a source-current variable

The rational scalar primitive retains the freedom

```
K -> K+v C(i,Jinv), v=e⁶,
L -> L+e^−1 C(i,Jinv),
L_e -> L_e+e^−2[−C−2i C_i−2Jinv C_Jinv].
```

The function C is not fixed to zero. It is a genuine two-variable parameter
for the compact and residue equations in (Remaining). A particularly useful
positive closure would be a C making L_e vanish. A necessary condition is

```
Z[(D−7)K/v]=0.
```

This condition has not been asserted or assumed. If it fails, the complete
rank-eight compact source and its zeta/omega companions in (Remaining) must
still be served. The coupled two-section rows are recorded in
`COUPLED-TORIC-ADJOINT.md`; their raw-xi residual cancels its finite and
infinity components together and cannot silently absorb an independent
omega coefficient.

`verify_theta_weighted_transfer.py` checks fourteen exact contiguity,
polynomial-representative, residue, product-rule, and density-weight
identities. The independent infinity derivation confirms the infinity sign
and the compact polynomial numerator. No original-target identity or Lean
proof follows yet.
