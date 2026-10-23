# An independent toric point-pair source generator

Status: literal source identities and annihilators. No primitive or certificate.

Use `Q=Aa²+Bb²+Cq²+Daq+Eq+T`, `ab=q³`, and
`J=aQ_a−bQ_b`. Put `eta_b=b dq/J`. At `q=0` the four finite points are

```
Pa±=(a=0,b=±b0,q=0), b0²=−T/B,
Pb±=(a=±a0,b=0,q=0), a0²=−T/A.
```

The rational differential and its normalized point-pair version are

```
zeta=b dq/q,
chi_a=zeta/b0.
```

`chi_a` has residues `+1,−1` at `Pa+,Pa−`. It has no pole at `Pb±`,
because there `b=q³/a`, and its numerator is `q²dq/a`.
It has fourth-order second-kind poles at the two infinities, with
**zero infinity residues**. In the projective chart
`a=1,q=u,t=u³/b(u)`,

```
zeta=[b b'/u³−2b²/u⁴]du,
Q=A+B b²+D u+C u²+E u⁴/b+T u⁶/b²=0.
```

Thus `[u³]b²=0` and `res(zeta)=−[u³]b²/2=0`. The higher poles are
retained, rather than removed by a claim that this is a simple-pole form.

All parameter derivatives below fix q and use the actual implicit lift

```
a_p=−a Q_p/J, b_p=b Q_p/J.
```

They give the **literal**, rather than fiber-exact, identities

```
partial_E zeta=eta_b,
partial_C zeta=q eta_b,
partial_D zeta=a eta_b,
partial_T zeta=eta_b/q.
```

Consequently the actual source is

```
tau=−partial_E² zeta=−partial_T partial_C zeta,
(partial_E²−partial_T partial_C)zeta=0.
```

For the normalized generator, `b0_T/b0=1/(2T)`, so

```
partial_E chi_a=eta_b/b0,
partial_C chi_a=q eta_b/b0,
partial_D chi_a=a eta_b/b0,
partial_T chi_a=eta_b/(b0 q)−chi_a/(2T),
[partial_E²−partial_T partial_C−(1/(2T))partial_C]chi_a=0.
```

These supply a new independent finite point-pair normal function, with
no extra infinity-residue companion. They do not assert that its pair
difference is torsion.

Under the physical base lift used in `actual_ruling_adjoints.py`, zeta's
scalar connection is `c_zeta=−u+v`; the normalized `chi_a` is invariant
under simultaneous norm-torus and coefficient scaling. A direct E/E
integration by parts leaves

```
G_zeta zeta,
G_zeta=−div_mu(ME VEsource)−ME c_zeta.
```

Its value at `R=S=z=k=1` is `−992/3`, so this single transport does
not itself close. The literal C/T and D identities permit other currents;
they are not excluded by that residual.

`verify_toric_point_pair.py` passes eleven exact symbolic groups,
covering the literal derivatives and source box, normalized operator,
finite point residues, other q=0 points, and infinity poles/residues.
Independent audit is requested in `audit/ruling/`.

## The third normalized source operator

Root's local-root residue argument supplies all three literal universal
GKZ boxes. Write the implicit polynomial in b as

```
P(b)=B b⁴+(Cq²+Eq+T)b²+Dq⁴b+Aq⁶.
```

The m-th coefficient derivative of a simple root b is
`(−1)^m(m−1)! Res_local[(product P_theta)/P^m db]`.
The products `P_A P_B P_T=P_C³=q⁶b⁶` coincide, so

```
(partial_A partial_B partial_T−partial_C³)zeta=0
```

literally at fixed physical q. Likewise `P_D²=P_A P_C` gives the
second quadratic box `partial_D²−partial_A partial_C`.

For the normalized coefficients of `../ruling-source/NORMALIZED-MODULI-DENSITY.md`,
put

```
A0=−c/3 partial_c−2d/3 partial_d−e/6 partial_e,
B0=−c/3 partial_c−d/6 partial_d−e/6 partial_e,
T0=−c/3 partial_c−d/6 partial_d−2e/3 partial_e.
```

The third compact operator and its `dc dd de` adjoint are

```
P3=A0(B0−1/2)(T0+1/2)−partial_c³,
P3*=partial_c³−(T0−5/3)(B0−1/6)(A0−7/6).
```

At fixed normalized q the normalized differential is not literally
annihilated: the changing coordinate scale adds a Cartan fiber derivative.
Writing `R=Lie_(q partial_q)`, `A=A0`, `B=B0−1/2`, `T=T0+1/2`, set

```
U=(A+B)T/6−AB/3,
V=T/36−(A+B)/18,
f3=−i_(q partial_q)[U chi_a+R V chi_a−R²chi_a/108].
```

Then `P3 chi_a=d_q f3`. Indeed the full universal derivative operators
are `A+R/6,B+R/6,T−R/3`, whose product is
`ABT+R U+R² V−R³/108`. This exact potential was independently
derived by the coupled-current agent and must be included when lifting a
compact source solution to an actual primitive.

`verify_normalized_third_box.py` checks the coefficient chain rule on
arbitrary monomial exponents, the formal adjoint by Laurent residue
pairing, the root-polynomial products, and the full Cartan expansion.
The operator data are in `normalized-third-box.json`.
