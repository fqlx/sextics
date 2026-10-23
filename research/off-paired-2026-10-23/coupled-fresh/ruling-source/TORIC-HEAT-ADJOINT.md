# Actual source and the toric-section heat adjoint

Status: exact source/annihilator formulas and constructive multiplier
search; no primitive or certificate.

Put `b0²=−T/B` and use the toric third-kind section

```
chi=b dq/(b0 q).
```

It has constant residues +1 and −1 at the two finite q=0 points with a=0.
It has zero infinity residues, but retains fourth-order infinity
second-kind poles. It is invariant under simultaneous norm-torus
coordinate/coefficient changes and common Q scaling. Its literal
coefficient identities include

```
partial_E chi=eta_b/b0,
partial_C chi=q eta_b/b0,
tau=−b0 partial_E² chi,
[partial_E²−partial_T partial_C−(1/(2T))partial_C]chi=0,
[partial_D²−partial_A partial_C]chi=0.
```

The first heat relation includes the T derivative of b0. No infinity
companion is discarded; every derivative of chi has zero residues and
retains the appropriate infinity principal parts.

Normalize A=B=T=1 as in `NORMALIZED-MODULI-DENSITY.md`, and write
`u=c−d²/4`. Then b0²=−1 is constant and

```
V=−(u/3)partial_u−(d/6)partial_d−(2e/3)partial_e.
```

The two normalized operators, with explicit fiber-exact corrections, are

```
P1=partial_e²−(V+1/6)partial_u,
P2=partial_d²+(u/3)partial_u²−(d/3)partial_d partial_u
   +(e/6)partial_e partial_u−(1/6)partial_u.
```

Changing the q coordinate contributes Cartan terms: the normalized
operators are not claimed to kill the literal q-fixed form. Their full
relations are `P1 chi=d_q rE`, `P2 chi=d_q rD`, where
`rE=−i_(q partial_q)(partial_c chi)/3` and
`rD=i_(q partial_q)(partial_c chi)/6`.
The complete third-box correction and all Green currents are saved in
`adjoint-reconstruction/CHI-THREE-OPERATOR-CURRENTS.md`.

Their adjoints for `du dd de` are

```
P1*=partial_e²−partial_u(V−4/3)
   =partial_e²+(u/3)partial_u²+(d/6)partial_d partial_u
     +(2e/3)partial_e partial_u+(5/3)partial_u,
P2*=partial_d²+(u/3)partial_u²−(d/3)partial_d partial_u
     +(e/6)partial_e partial_u+(2/3)partial_u.
```

The actual source is `−b0 H partial_e² chi du dd de`. Two integrations
by parts leave `−b0 H_ee chi`. Thus a constructive sufficient condition
is to produce multipliers w1,w2 satisfying

```
P1*w1+P2*w2=H_ee.                                  (1)
```

This note/search uses the positive H_ee convention. The reconstruction
note writes its potentials against `−H_ee`; a successful search potential
is therefore negated when substituted into that note's current formula.

Unlike the single ruling-pair annihilator, this system requires no extra
infinity equation. A successful current still requires its full Green
concomitant, trace descent, the immutable rational source identity, and
the repository's formal verification workflow.

## Rational physical form used for multiplier construction

Use the exact physical lifts `YE,XC,YD,VT` of the universal directions
`partial_E,partial_C,partial_D,partial_T`. Define

```
epsilon=e/E=T^(−2/3)(AB)^(−1/6),
gamma=d/D=T^(−1/6)A^(−2/3)B^(−1/6),
Z=T VT,
VA=−(C/3)XC−(2D/3)YD−(E/6)YE.
```

Here Z represents normalized V and VA represents normalized
`A partial_A`. Direct coordinate transformation gives

```
epsilon² P1* F
 =[YE²−(YE log epsilon)YE−T^(−1)XC o(Z−4/3)]F,
epsilon² P2* F
 =(A/T)[YD²−(YD log gamma)YD−A^(−1)XC o(VA−5/6)]F,
epsilon² H_ee=[YE²−(YE log epsilon)YE]H.
```

All coefficients become rational in the physical variables, because
`epsilon²/(c/C)=1/T` and `gamma²/(c/C)=1/A`.
Writing `wi=H fi` makes equation (1) an explicit linear rational PDE
for the physical functions fi, with no need to evaluate fractional
normalizing powers.

`search_heat_multiplier.py` evaluates that equation by exact finite-field
Taylor jets to construct rational candidates. H is represented by its
normalized local Taylor series, so fractional powers have rational jet
coefficients. Any modular hit must be reconstructed and verified as a
literal identity before it can support a certificate. Failed trial spans
are solely search feedback and have no global nonexistence meaning.

## Third box and source-preserving finite characters

The third normalized adjoint is

```
P3*=partial_c³−(VA−7/6)(VB−1/6)(VT−5/3),
VB=−(c/3)partial_c−(d/6)partial_d−(e/6)partial_e.
```

It has the known fiber-exact Cartan correction from the reconstruction
note; `P3*(1)=35/108` does not by itself invert the operator on H.
Use potentials `w1=Hf1,w2=Hf2,w3=H alpha^(-1)f3`, where
`alpha=c/C=(TAB)^(-1/3)`. Multiplication by epsilon² makes all three
physical operators rational. In particular, setting `a=XC log alpha`,

```
epsilon² P3*(F/alpha)
 =AB(XC−3a)(XC−2a)(XC−a)F
  −T^(-1)(VA−7/6−VA log alpha)
         (VB−1/6−VB log alpha)(VT−5/3−VT log alpha)F.
```

Over `C(R,S,Z=z^6)`, the physical source and operator characters occupy
the finite block `k^l z^n`, `0≤l≤5`, `n=0,2,4`.
The source character is `(z,k)=(−2,0)`. The three operators have shifts
`{(−2,0),(0,−1)}`, `{(−2,−2),(0,−1)}`, and
`{(0,−3),(0,0)}`, respectively. These follow directly because YE is
z^(-1) times a character-zero field, XC is k^(-1) times such a field,
YD has character (z k)^(-1), and VA,VB,VT have character zero.
`search_prepared_multipliers.py` uses this complete finite block and the
source-induced branch divisor Delta to construct further potentials.
