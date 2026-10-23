# Independent compact connection and exact original-source audit

The actual off-paired source has an explicit, fully audited compact rank-eight
representation. Its rational primitive remains open. Nothing here establishes
a certificate, Lean proof, protected CI result or acceptance.

## Generic connection and literal primitives

The rational descended curve is

```
a*y=x³,
y²+v(a²+i*x²+j*a*x+x+1)=0,
Jbar=v(2a²+j*a*x)−2y².
```

The compact basis is `nu_N=v*N dx/Jbar`, with numerators

```
1, x, x³, x⁴−v*Cp*(Cp−j²)*x²/8,
a, a*x+j*x²/2, y, y*x,
Cp=i−j²/4.
```

Columns of each connection matrix differentiate the corresponding basis form.
Both horizontal derivatives at fixed v and `V=6v partial_v` have explicit
rational fiber primitives. They include the essential fixed-x Cartan term
`−contraction_(x partial_x)(nu)` in the V direction.

The independent `verify_generic_compact_connection.py` reconstructs the
implicit parameter variation and fiber derivation from the two defining
curve equations. It imports neither the primary builder nor its solver.
It passes 82 exact generic groups: nine full cleared curve identities,
all 64 deck-descended compact entries, eight zero residue columns, and
the third-kind diagonal before restriction to the compact space.

`verify_full_base_connection.py` independently verifies 886 generic groups:
the eighteen full c,d derivative identities, every descended i,j,V connection
and fiber-primitive entry, and all 192 curvature entries for the pairs
(i,j), (i,v), and (j,v). Thus the complete compact connection is flat and
the literal correction terms are verified, rather than inferred from
cohomology or a point specialization. Hashes of all checked packets are
recorded in the result files.

## Exact finite-residue serving and the compact Green source

Let `Hsrc=e^-5 hsrc`, and let `f=e^-5 F`, `g=e^-5 G`, `h=e^-1 Hpot` be the
source-bound three-adjoint potentials. For the scalar Green currents evaluated
at the constant residue, put

```
Vbase=Hsrc_e partial_e+B_PE(f,1)+B_PD(g,1)+B_P3(h,1),
M=e^-7 K, Z=−B0, X=Vbase−MZ.
```

The actual scalar reduction gives `div X=−M/2`. Therefore the finite Pa
three-form has the explicit two-form primitive `±sqrt(-1) contraction_X(mu)`.
The entire curve-valued kernel satisfies

```
M(B0−1/2)zeta=div(X*zeta)−Vbase(zeta).
```

Its remaining components are compact, literally

```
zeta_c=b*q dq/J, zeta_d=q³ dq/J, zeta_e=b dq/J.
```

Thus neither a finite-section nor an infinity-section component has been
dropped. `verify_compact_three_row_source.py` passes fifteen exact formal
Green, implicit-fiber, density-weight and product-rule groups. The explicit
rational three-row formula is recorded in its JSON result. The large K and
its N-only Hermite expansion cancel from that compact representation.

The same original source has an even simpler one-row representative:

```
−Hsrc*zeta_ee = −partial_e(Hsrc*zeta_e)+Hsrc_e*zeta_e.
```

The compact forcing in volume `di dj dv` is therefore
`(D−5)hsrc/(6v²)*e_b`, with `e_b` the seventh compact basis vector and
`D=6v partial_v−2i partial_i−j partial_j`.

## Full-base Euler first current

Set `t=hsrc/(6v²)` and `GammaD=GammaV−2i Gamma_i−j Gamma_j`. In flat
volume `mu=di dj dv`, `div D=3`, so

```
P_i=−2i*t*e_b, P_j=−j*t*e_b, P_v=6v*t*e_b,
source−covariant_div(P)=t(4e_b−GammaD*e_b).
```

For relative curve forms first, the literal three-current is

```
Jbase=−sum_p (nu dot P_p) wedge contraction_p(mu),
Jfiber=−t*fD_b*mu,
fD_b=fV_b−2i*fi_b−j*fj_b.
```

`verify_source_euler_current.py` passes 32 exact groups: flat-volume
divergence, the constant four, source density weights, the factor `2j`
when converting between `di dJ` and `di dj`, the exterior-current signs,
all eight residual entries, all sixteen literal fiber-primitive entries,
and input hash bindings.

The physical inverse-root cover is retained. With

```
T=1+w³, N=9i²w²−16j²T,
v=64j²wT²N/[9i²(256T⁵N+729i⁶j²w⁶)],
hsrc*v_w/v²=54i³wT/(j²N),
```

the remaining actual source in volume `di dj dw` is exactly

```
9i³wT/(j²N) * (4e_b−GammaD*e_b).
```

This entire eight-component source remains to be served. The Euler step can
also be viewed as undoing the first integration by parts: it is the direct
compact representation of the original second derivative. In fact
`nu_b=e⁴ zeta_e`; after retaining the moving-x Cartan term,

```
e⁵ zeta_ee=(GammaD−4)nu+d_x(fD_b+contraction_(x partial_x)(nu_b)).
```

Consequently a direct original-source fiber primitive is
`−t*(fD_b+v*x*y/Jbar)*mu`, with the same compact remainder above. This
interpretation prevents a coordinate reconstruction from being mistaken for
an additional independent solution of the compact integration problem.

## Complete genus-two interface retained for scalar residue work

In `u=j²/i²`, the inverse root is exactly

```
h²=1/v=A+B i⁶,
A=36(1+w³)³/(u*w),
B=6561w⁵/[64(9w²−16u(1+w³))(1+w³)²].
```

The scalar residue family is isotrivial genus two when u,w are held fixed.
The four compact differentials `i^n di/h`, n=0,1,3,4, have the literal
connection

```
nabla omega_n=[(n−2)dlogA−(n+1)dlogB]omega_n/6
              +d_i[i^(n+1)(dlogB−dlogA)/(6h)].
```

Possible residue classes n=−1 and n=2 are retained as well. Thirty exact
groups in `verify_isotrivial_pa_interface.py` check the physical density,
all six connection classes, and deterministic monomial reduction recurrences.
No second-kind component is removed by a first-kind-only approximation.

## Actual j current and a rational third primitive

The new source-serving parameter primitive is independently verified by
`verify_j_source_current.py` (45 exact groups). In the same compact order,
put

```
U=[v(5j²−12i)/48, v(5j²−12i)/48, −1, 2,
   −5jv/24, jv(15j²−52i)/96, 0, −j/2].
```

It has zero infinity companion and satisfies the complete generic identity

```
partial_j U+Gamma_j U=(4I−GammaD)e_b.
```

It follows from the literal rational moment `Psi_j=y² dx/(2x⁴)` and its
full nine-class plus rational-fiber reduction. All nine entries of the
moment derivative, the Euler shift, the compact source equation and the
fiber reduction are checked independently. For the actual density t, this
gives current `P_j=tU` and the retained source `−partial_j(t)|i,v * U`.
The source is not served by treating t as constant.

The full physical Piola transformation and fiber terms are also verified:

```
P_j,physical=v_w*t*U, P_w,physical=−v_j*t*U,
remaining=−v_w*(partial_j(t)|i,v)*U,
partial_j|i,v=partial_j|i,w−(v_j/v_w)partial_w.
```

There is a useful literal hierarchy that avoids a logarithmic third current.
Set `V0=i*x²+x+1`. With `Dnorm=Dnative+Lie_(x partial_x)`, the three
rational one-forms

```
U1raw=−v*y² dx/(x³*Jbar),
U2raw=−y³ dx/(3x⁷),
U3raw=[−y²/(6x⁵)+V0*y⁴/(12x¹¹)+y⁶/(6v*x¹¹)]dx
```

satisfy literally

```
partial_j U3raw=U2raw,
partial_j U2raw=U1raw,
partial_j U1raw=(4−Dnorm)nu_y.
```

The raw third moment has `(1/2)log(y) dx`, but its logarithm cancels under
`1−Dnorm`; the remaining constant `−3dx/2` is rational exact. Nine generic
implicit-curve identities in `verify_rational_euler_j_hierarchy.py` check
this cancellation and the complete chain.

All finite and infinity poles of these raw forms are retained. They are
not asserted to be compact representatives. They provide rational higher
currents with the corresponding exact fiber corrections; after three
weighted integrations by parts, the source still contains `−t_jjj U3raw`.
A finite full-source closure has not been obtained.
