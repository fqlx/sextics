# The actual K-driven coupled system in rational invariants

Status: an explicit source-driven closure system, not solved. It retains the
two-section residues and a nonzero compact target. No multiplier degree or
denominator bound is imposed here.

Use the rational invariant derivations from `RATIONAL-THREE-ADJOINTS.md`:

```
i=c/e², Jinv=(d/e)², v=e⁶,
A=partial_i at fixed(Jinv,v), B=partial_Jinv at fixed(i,v), Z=v partial_v,
D=6Z−2iA−2Jinv B.
```

The derivations A,B,Z commute. In physical root coordinates `(i,Jinv,w)`,
they include the inverse-root derivatives of w. All operator products below
have the rightmost operator acting first.

The actual scalar construction specifies rational K by

```
Ssrc−PE(Fpot)−PD(Gpot)−P3(Hpot)=(Z−1)K,
L=e^−7 K, U=(D−7)K, L_e=e^−8 U.
```

The additive freedom `K+v C(i,Jinv)` remains available. The regularized
choice from `genus4-gm-independent/actual-rational-k-normalization.json`
has `K=O(w²)` at w=0 and is a useful representative, not a restriction on C.

Put

```
u=i−Jinv/4, Cp=e²u,
s=d Cp/2, kappa=d(Cp³+8)/16,
f=kappa/s=(Cp³+8)/(8Cp),
r=u²/8+1/(u v).
```

Then the normalized coefficients in the source-driven coupled pair of
`THETA-WEIGHTED-KERNEL-CURRENT.md` are exactly

```
Ztarget=(e/2)L_e=e^−7 U/2,
Xtarget=f L_e=e^−4 r U.
```

The full raw-xi infinity coefficient is `s Xtarget=kappa L_e`. It must be
retained under every operator before adjunction.

## Rational operators for all four cross potentials

Write the four cross potentials as

```
w1=e^−3 F, w2=e^−4 G, w3=e^−6 H, w4=e^−7 I.
```

Their zeta coefficient is e^−7 times

```
Zcross=A²F+A(D−4)G
       −(D−6)(Z+Jinv B)H
       +(Z+D/2−3)(Z+Jinv B)I.
```

Their raw-xi coefficient is e^−4 times

```
Xcross=−(D−3)ZF+(Z+D/2−1)ZG
       +v^−1[A²H+A(D−7)I].
```

Thus all four cross rows remain rational in the physical source field.
The factors v^−1 in the two symmetric rows are forced by their relative
weights; dropping them changes the target.

## Rational self rows for the second toric section

For zeta self potentials of weights e^−5,e^−5,e^−1, the rational rows are

```
OZ1=(D−6)(D−5)+A(Z+D/2−2),
OZ2=4Jinv B²+2B+A(Z+Jinv B),
OZ3=A³+v(Z+Jinv B+1)Z(Z+D/2+1).
```

For raw-xi self potentials of weights e^−2,e^−2,e², the corresponding
rational rows are

```
OX1=(D−3)(D−2)+A(Z+D/2),
OX2=4Jinv B²+2B+A(Z+Jinv B),
OX3=A³+v(Z+Jinv B+1)(Z+1)(Z+D/2+3).
```

These follow from the complete formal adjoints in
`COUPLED-TORIC-ADJOINT.md`; the changes in constants come from both the
xi normalizer and the potential weights.

## The source-bound equations and the remaining compact source

The concrete enlarged scalar equations are

```
sum_j OZj fj+Zcross=U/2,
sum_j OXj gj+Xcross=r U.
```

They have not been solved. A solution would supply the complete toric
currents for the actual K-dependent coefficients. It would still leave the
following exact, specified compact source:

```
Ccompact=−L_e Omega−f L a dq/Jcurve−kappa L partial_e(omega),
omega=q²dq/Jcurve,
Omega=Theta+(e/2)zeta+d_q[b³/(3q)]+kappa omega.
```

All eight compact components of Ccompact must be served using the full
connection. The infinity correction in this expression and the scalar
equations do not justify deleting it. The overall current is negated when
reconstructing the actual source `−H zeta_ee` from the positive Ssrc
convention used in the scalar construction.
