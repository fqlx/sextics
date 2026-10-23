# Independent toric point-pair and heat-current audit

The literal toric source identities, the normalized quadratic adjoints, and
the current finite-field implementation check out. No candidate was accepted
and no search was rerun as part of this audit. No certificate has been found.

The independent artifacts are:

- `verify_toric_fraction.py` and `toric-fraction-results.json`: 14 exact
  groups using standard-library Fraction sparse rational arithmetic.
- `verify_heat_implementation_fraction.py` and
  `heat-implementation-fraction-results.json`: 185 checks using exact formal
  operator adjunction and independent Fraction third-order Taylor jets.

The implementation snapshot checked is
`coupled-fresh/ruling-source/search_heat_multiplier.py`, SHA256
`d374783a275f2df4559f448a6a5b21cae334488acded3fd34d0a473a8a9de4b5`.
Its modulus is 1009 and its Taylor order is three. That module is imported
only to sample its outputs after the independent geometry has been computed;
no primary mathematical checker or symbolic generator is imported.

## Literal toric generator

Use the target-bound canonical curve and source orientation from
`RULING-SOURCE-AUDIT.md`:

```
ab=q^3,
Q=Aa^2+Bb^2+Cq^2+Daq+Eq+T,
J=aQ_a-bQ_b,
η_b=b dq/J,
ζ=b dq/q,
χ=ζ/b0, b0^2=-T/B.
```

The exact, physical-`q`-fixed lifts
`a_θ=-aQ_θ/J`, `b_θ=bQ_θ/J` give the literal identities

```
∂Eζ=η_b, ∂Cζ=qη_b, ∂Dζ=aη_b, ∂Tζ=η_b/q,
(∂E^2-∂T∂C)ζ=0,
∂Tχ=η_b/(b0q)-χ/(2T),
[∂E^2-∂T∂C-(1/(2T))∂C]χ=0.
```

Consequently the actual fiber source is
`τ=-∂E^2ζ=-∂T∂Cζ=-b0∂E^2χ`. The exterior base density remains
`dr∧dk∧dz/(9r)`; this calculation does not integrate it away.

At `Pa±=(0,±b0,0)`, `q` is a generic local parameter, giving residues
`(+1,-1)` for χ. At `Pb±`, the norm relation makes
`ζ=q^2dq/a`, which is regular. In the projective chart
`a_proj=1,q_proj=u,t=u^3/b(u)`, the quadric gives

```
b(u)^2=-A/B-(D/B)u-(C/B)u^2+0u^3+O(u^4).
```

The full negative principal part is therefore

```
ζ=[2A/(B u^4)+3D/(2B u^3)+C/(B u^2)]du+regular.
```

The infinity residues vanish at both points, while the fourth-, third-,
and second-order second-kind data remain. χ divides this expression by
`b0`. No claim that χ has only simple poles is used.

## Normalized adjoints

In normalized coordinates `(c,d,e)`, set

```
A0=-(c/3)∂c-(2d/3)∂d-(e/6)∂e,
T0=-(c/3)∂c-(d/6)∂d-(2e/3)∂e.
```

The forward quadratic operators are
`PE=∂e^2-(T0+1/6)∂c` and
`PD=∂d^2-(A0-1/3)∂c`. Set `u=c-d^2/4`; this triangular coordinate
change has Jacobian one. The independent checker constructs differential
operators as sparse polynomial coefficients times partial derivatives,
composes them using the full Leibniz rule, and derives their adjoints by
`(a∂^I)*=(-∂)^I a`. It verifies exactly that

```
PE*=∂e^2-∂u(T0-4/3),
T0=-(u/3)∂u-(d/6)∂d-(2e/3)∂e,
PD*=∂d^2+(u/3)∂u^2-(d/3)∂d∂u
    +(e/6)∂e∂u+(2/3)∂u.
```

Both double adjoints recover the forward operators. These are exact
operator equalities; the test does not infer an adjoint from a few
evaluations.

## Independent check of the actual implementation

For each of five rational points compatible with `k^6=RS`, the verifier
constructs normalized-coordinate jets directly:

```
c=C T^(-1/3)(AB)^(-1/3),
d=D T^(-1/6)A^(-2/3)B^(-1/6),
e=E T^(-2/3)(AB)^(-1/6),
A=1+R, B=1+S, C=k/3, D=zk/2, E=z/2, T=1+z^6.
```

It inverts their three-by-three Jacobian over Fraction jets. This supplies
the normalized-coordinate partial derivatives without using the submitted
physical lift formulas. The cubic cover `k^6=RS` and every chain-rule term
are retained.

The source density is independently reconstructed as

```
H=L ε μ/(c d e Jlog),
L=T^(-1/6)A^(-1/6)B^(-2/3),
ε=T^(-2/3)(AB)^(-1/6),
μ=1/(108k^5),
Jlog=det ∂(log c,log d,log e)/∂(R,S,z).
```

The checker separately verifies the full third jet of
`Jlog=Delta/(36RSzABT)`. It derives the normalized `H/H(point)` jets
from these factors, rather than importing the implementation's closed
exponent formula. All resulting third jets agree modulo 1009 with the
implementation.

On eleven rational functions at each point, the submitted first two
operators agree with `ε^2 PE*` and `ε^2 PD*`. For the third operator,
`α=(TAB)^(-1/3)`, the checked expression is

```
ε^2 P3*(α^-1 F),
P3*=∂c^3-(A0-7/6)(B0-1/6)(T0-5/3).
```

This explains the implementation's `AB` coefficient before its triple
`C`-derivative term and `1/T` before its Euler product. Every derivative
of α remains. The independent normalized-Jacobian calculation agrees
with all three implemented operators and the forcing term at the five
points. As a useful calibration,

```
op3(α/α(point))=35/(108T),
```

which is `35/216` at `R=S=z=k=1`. At that point the implemented forcing
is `992/3`. Exact values and their finite-field reductions are saved.

The implementation uses Python integer arithmetic and modular inversion;
there is no floating-point exactness issue in these routines. The tests
are local implementation comparisons, not global proof that a future
sampled solution is a rational identity. A hit still requires fresh-point
checks, characteristic-zero reconstruction, all exact fiber potentials,
trace descent, and the original certificate side conditions.

## Reconstruction conventions

The search's displayed equation has right-hand side `+H_ee`. The literal
Green-current reconstruction in
`ruling-source/adjoint-reconstruction/CHI-THREE-OPERATOR-CURRENTS.md`
uses `-Hsrc_ee` for source `-Hsrc χ_ee`. A positive-right-hand-side
candidate can be negated, but this sign must be applied when building
the actual current.

There is also an overall constant to restore: the normalized differential
has `b0'^2=-1`, so the source-density formula
`-H∂eη'_b` equals `-b0'H χ_ee` after choosing `b0'=±i`. It may be
absorbed in search coefficients, then must be restored in a literal
source identity. The source agent was notified of both conventions.

No finite search failure is interpreted here as an exclusion, and no
existence or nonexistence result for a full primitive follows from this
audit.

## Independent Newton check of the complete physical χ jets

The later `verify_chi_jets_newton.py` audit checks all nineteen saved
first-, second-, and third-order physical derivatives of χ at
`R=S=z=k=1` over 1009. At twelve fresh affine points of the actual curve,
it solves

```
B b^4+(Cq^2+Eq+T)b^2+Dq^4 b+Aq^6=0
```

by multivariate truncated Taylor Newton iteration, fixing physical `q`.
The independent jets retain `k^6=RS` and multiply the root by
`[(T/T0)/(B/B0)]^(-1/2)` to obtain `b0(point)` times the normalized χ
coefficient. It does not import the primary derivative formulas or code.

At each curve point, it separately evaluates the saved compact forms and
direct `q` derivatives of the saved rational exact primitives. All
nineteen resulting identities match the Newton derivatives: 228 literal
checks passed. It also independently recomputes rank eight and pivot
labels `R,S,z,RR,RS,Rz,SS,RRR` for the saved compact coordinate matrix.

Results and source hashes are in `chi-jets-newton-results.json`.
The checked compact/primitive packet is
`genus4-gm-independent/chi-physical-third-jets-results.json`, SHA256
`a1e2912a7aca53f901b03fa74742eed8e36d323d7d310eb8497fce1872a99784`.
This independently checks the local target derivatives and their saved
representatives; it does not reprove the primary global RR-completeness
or ideal-reduction arguments. The complete local compact span still does
not supply an actual source primitive or a characteristic-zero current.
