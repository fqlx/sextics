# An exact translated current for the actual cubic source

This constructs a rational primitive for the **sum of four translated
fiveforms**. It does not yet give a primitive for the immutable branch
source. `cubic-two-torsion-current.py` checks all rational identities.

Use the cubic-ray notation from `CUBIC-RAY-COMPANION.md`. On the actual
elliptic companion,

```
g(r)=r³+A r+D=W²,
A=BC, D=HC²,
alpha=C r²/(2g²) Omega4∧dr.
```

Let `e1,e2,e3` be the roots of `g` in its finite splitting field, and put
`Di=g'(ei)=3ei²+A`. Define the rational function and source coefficients

```
K(r)=−C/2 * sum_i ei²/[Di²(r−ei)],
Ri=C A ei/Di³.
```

Exact partial fractions give the full source identity

```
alpha = d(K Omega4) + Omega4∧sum_i Ri dlog(r−ei).
```

Here `dlog h` denotes the rational oneform `dh/h`; no logarithm is used as
a coefficient. Base derivatives of `K,ei,Ri` wedge to zero with `Omega4`.
The coefficient is the actual physical normal residue:

```
ei=C si, Di=C f_s(si),
Ri=B si/f_s(si)³,
sum_i Ri=0.
```

Because the map `r` has ramification index two at `Qi=(ei,0)`, the ordinary
logarithmic residue of `alpha` on the companion along `Qi` is
`2 Ri Omega4`. No pole correction at a physical branch has been dropped.

## Exact translation and trace

Translation `Ti` by the two-torsion section `Qi` is

```
Ti(r)=ei+Di/(r−ei),
Ti(W)=−Di W/(r−ei)².
```

Together with the identity, these are the four translations indexed by
`E[2]`. They fix the base and preserve the companion equation. For every
root `ej` there is an exact product identity

```
product_{h in E[2]} (Th(r)−ej) = Dj².
```

Its logarithmic differential has only base components, so

```
Omega4∧sum_h Th*[dlog(r−ej)] = 0.
```

Consequently the **actual rational translated-current identity** is

```
sum_h Th*alpha = d[Omega4 * sum_h Th*K].
```

The sum includes infinity: a translation sends one finite two-torsion
section to infinity, and the product identity records this contribution.
This is a finite-extension algebraic identity, not a fixed-`j` analytic
contraction.

## Remaining construction

The cancellation is collective. At any chosen two-torsion section, the
four translated logarithmic residues sum to zero. This verifies the
translated identity but does not express an individual `Ri Omega4` as a
rational derivative. In particular, normalized trace or a group average
cannot be inverted on the character components which the trace kills.

An application to the target still needs an independent way to isolate
the physical source from this translated sum, or a rational primitive for
its source coefficient. The identity does not establish such a primitive.
