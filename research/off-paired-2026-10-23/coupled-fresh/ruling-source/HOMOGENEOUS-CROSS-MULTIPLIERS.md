# Explicit residue-free cross-current multipliers

This is a constructive multiplier family, not a solved source equation.
Use the complete companion cross relation and its Cartan primitive in
`../infinity-horizontal/COMPANION-TORIC-CROSS.md`. Its normalized adjoint
contributes `partial_c^2 W` to zeta and the pair
`R_b W, s R_b W` to the corrected companion and omega, where

```
B0=-(2c partial_c+d partial_d+e partial_e)/6,
R_b W=partial_e(B0-1/2)W,
s=d(c-d^2/4)/2.
```

Both companion components cancel if `R_b W=0`. Since
`R_b W=(B0-2/3)partial_e W`, every

```
W=e^(-3) F(i,j)+G(c,d), i=c/e^2, j=d/e
```

lies in this kernel. The first term has weighted degree -3 for weights
`(c,d,e)=(2,1,1)` and the second is e-independent. This states a sufficient
family and does not assume it classifies every algebraic kernel solution.
In particular,

```
partial_c^2[e^(-3) F(i,j)]=e^(-7) F_ii(i,j).
```

The actual physical normalization makes this family quite concrete:

```
i=4kT/(3z^2), j^2=k^2T/A,
A=1+R, B=1+S, T=1+z^6, k^6=RS.
```

Put `alpha_c=c/C=(TAB)^(-1/3)` and
`epsilon=e/E=T^(-2/3)(AB)^(-1/6)`. The appropriate comparison with the
physical source is

```
W=Hsrc (alpha_c^2/epsilon^2) fW,
fW=[2k Delta/(z^2 A)] F(i,j).
```

This equality follows by substituting the exact Hsrc from
`NORMALIZED-MODULI-DENSITY.md`; all roots use the same coefficient cover.
For rational F in i,j^2, fW is rational in the actual physical field.
It has the source-induced Delta factor in its numerator, rather than an
arbitrarily chosen pole. For example,

```
F=i^2:
W=c^2/e^7,
fW=32k^3 Delta T^2/(9z^6 A),
partial_c^2 W=2e^(-7).
```

This provides a new residue-free forcing term to combine with all three
chi box adjoints. It does not identify the actual Hsrc_ee with that term.
The full coupled source match and the literal original certificate remain
open.

The B0 flow itself is rational after fixing i,j^2: using z as parameter,

```
k=3i z^2/(4T), R=k^2T/j^2-1, S=k^6/R.
```

These formulas can be used for algebraic source reduction along that flow.
They do not authorize integrating the scalar density without its curve
differential or dropping a trace character.
