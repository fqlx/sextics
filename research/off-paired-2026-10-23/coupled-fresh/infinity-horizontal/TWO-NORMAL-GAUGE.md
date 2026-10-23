# Source-preserving infinity gauge adapted to both normal coefficients

No certificate is claimed. This gives an exact operator gauge and rational
partial primitive of the actual infinity matching source. Its retained
remainder still needs a geometric or rational-current completion.

Use the notation in `../rank4-relative/INFINITY-ORE-SOURCE-MATCH.md`:
`L* A+M* B=1`, where `A=Uop*`, `B=Vop*`. The exact Ore syzygy

```
R L=S M
```

is recorded at general H in `source-gauged-ore.json`. Its adjoint permits
source-preserving changes

```
Anew=A−R* E, Bnew=B+S* E.
```

The Euler identity

```
S*(Delta² C^n)
 =2835 H² C^(n+2)(n−1)²(2n−5)(2n+1)
  −2066715 H⁶ C^(n−4)n(n−3)(n−2)(n+1)
```

makes the source-adapted choice

```
E=11 Delta² C(2theta−3)/(1786050 H⁴), theta=C D_C.
```

Its two coefficients are selected to annihilate C and C². Exactly

```
B12=1/630 [ (C³/H²)(44theta²−35)
                −(729H²/C³)(11theta²−39) ]
             (2theta+3)(theta−1)(theta−2),
L* A12+M* B12=1.
```

The coefficient multipliers in the square brackets act on the left;
the operator factors to their right act first. B12 annihilates C, C² and
C^(−3/2). The actual physical D_C still acts on a. It is not valid to replace
D_C by the derivative keeping a fixed.

`two-normal-gauge.json` contains all ordinary D_C coefficients for A12 and
B12. `verify_two_normal_gauge.py` checks the complete operator identity and
right factorization by `(theta−1)(theta−2)`. The original general-H syzygy
and the simpler C²-only gauge are independently checked in
`verify_source_gauged_ore.py`.

## Explicit rational source current

Put

```
Rnormal=−27C³/a+(81/4)Cz²a−(27/16)z³a²,
k=(81/2)C²z,
ell=log a,
phi=D_H Rnormal−k D_H ell=q³/P_a.
```

The notation ell below abbreviates its rational derivatives only. Define

```
Q=B12(phi)/6−B12(theta Rnormal)/(9H)
               +B12[theta(k ell)]/(9H),
S=B12 theta(2theta−3)(Rnormal−k ell)/(27H²).
```

All undifferentiated ell coefficients vanish because B12(k)=0. Thus Q and S
are actual rational functions on the physical coefficient field. Exactly

```
B12(phi_H/6)=T Q+S.
```

For the elementary-shifted original source `−C D_C(phi)/(9H)`, remove the
first term `B12(phi)/6` from Q. The same S remains. Eight symbolic checks in
`verify_two_normal_curl.py` establish the full identity, rationality and
agreement with the Ore gauge, without assuming anything about the derivatives
of a beyond the stated actual normal-antiderivative identity.

`evaluate_two_normal_remainder.py` uses independent Fraction power series of
the physical implicit a(C) branch through `(a,C,z,H)=(1,1,1,969/64)`. Its
retained S is nonzero. This checks the scope of the partial primitive; it is
not an exclusion of other gauges or currents.

## Remaining geometric task

Source cancellation does not require S itself to be an exact horizontal curl.
The infinity current may correspond to any closed rational two-form beta on
the actual three-dimensional physical base, with

```
beta restricted to C=b H^(2/3) = −S dH wedge dz.
```

For example, closed logarithmic forms contribute

```
beta=dlog(f) wedge dlog(g),
S=−[(T f/f)(D_z g/g)−(D_z f/f)(T g/g)].
```

A successful surface reduction may therefore leave a nonzero flat boundary
class. It must exhibit its closed form and compatibility with the actual
source; vanishing of an isolated local type is not enough. This route and
arbitrary independent horizontal corrections remain open.
