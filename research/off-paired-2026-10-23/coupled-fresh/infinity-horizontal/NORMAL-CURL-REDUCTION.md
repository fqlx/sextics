# Rational partial current for the infinity residue equation

This is an actual partial curl, with a retained nonzero source. It is not a
certificate, and it does not exclude a completion or another infinity current.

Use `rank4-relative/INFINITY-ORE-SOURCE-MATCH.md`. Let `B=Vop*`,
`theta=C D_C`, `T=D_H+2 C D_C/(3H)`. Exactly

```
B=−C³/(630H²) (2theta+3)(46theta²−105theta+70)
  +729H²/(630C³) (theta−2)(theta−1)(23theta+51).
```

The actual coefficient derivations are those of `P(a,H,C,z)=0`, not fixed a.
The operator B commutes with T and D_z. Therefore B takes every rational curl
`D_z P−T Q` to another rational curl.

Put

```
R=−27C³/a+(81/4)Cz²a−(27/16)z³a²,
k=(81/2)C²z, ell=log a.
```

The notation ell is used only to state derivatives: `D_i ell=D_i(a)/a`.
No logarithmic coefficient is permitted in the actual current. The exact
physical identity is `phi=D_H R−k D_H ell=q³/P_a`. Also

```
W_R=−81C²z²/(4a),
partial_a R+partial_z W_R=q³/a².
```

This ordinary density primitive alone does not integrate the compact kernel.

For the corrected infinity source `xi=B(phi_H/6)`, define

```
gamma=B theta(k)=−(198/5) C⁵z/H²,
Fplus=B theta(k ell)−gamma ell,
Kplus=B[k (theta+2)(2theta+1)ell]−gamma ell,
A=−(22/5) C⁵/H³,
g=A z²/2,
Qstd=B phi/6−B theta(R)/(9H)+Fplus/(9H),
P0=g T(ell), Q0=g D_z(ell),
S=B theta(2theta−3)R/(27H²)−Kplus/(27H²)
  +A z² D_z(ell)/(6H).
```

Both Fplus and Kplus have zero coefficient of undifferentiated ell. They
are finite rational expressions in `D_C^j(a)/a` and their derivatives.
Consequently every displayed current coefficient `P0,Q0,Qstd` is rational.
The exact source-carrying identity is

```
xi = D_z(P0)−T(Q0−Qstd)+S.
```

For the elementary-shifted original source
`xi_original=B[−C D_C(phi)/(9H)]`, remove `B phi/6` from Qstd; the same S
remains. Signs follow the convention `xi=D_z P−T Q`.

`verify_normal_curl_reduction.py` proves eight exact symbolic identities,
including this formula for arbitrary R and ell before inserting their actual
physical values. `evaluate_normal_remainder.py` uses an independent
standard-library Fraction jet implementation of the actual implicit branch.
At `(a,C,z,H)=(1,1,1,969/64)`, it finds

```
S=−6829234040212584977379183316315595842442325139
   /19471722368923197781899729602257856539422720.
```

Thus this partial curl has not closed the source. No all-pole conclusion is
claimed. In particular, freedom from Ore syzygies, other infinity residue
currents, and arbitrary independent horizontal currents remains available.
