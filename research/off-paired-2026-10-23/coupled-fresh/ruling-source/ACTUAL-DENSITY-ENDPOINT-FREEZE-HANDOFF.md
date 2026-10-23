# Actual-density / endpoint freeze handoff — 2026-10-23

Status: **UNSOLVED**. Research stopped at the user's request. This note records the final density route; it supplies no certificate or completed source primitive. No external write was made by this agent.

## Exact completed interfaces

- `full-base-connection/rank8-ij-connections-results.json` and `rank8-v-literal-primitives-results.json` give the generic rank-eight compact connection in native `(i,j,v)`, with literal fiber primitives. The V primitives include the mandatory negative Cartan term from `x=e q`. The full rank-nine infinity direction is retained before compact restriction.
- `audit/theta/verify_full_base_connection.py` and `full-base-connection-audit-results.json` independently passed **886 global exact groups**, including all connection/primitives and all 192 flatness entries. These audits were completed before this freeze.
- `full-base-connection/source-euler-current-results.json` and `audit/theta/source-euler-current-audit-results.json` bind the actual source to the Euler residual; the independent audit passed **32 groups**. The Euler residual is also a direct compact representation of the original source, so it must not be counted as serving a second independent compact component.
- `full-base-connection/j-source-primitive-results.json` and `polynomial-potential-rows-results.json` contain Fresh's polynomial compact moment identities. Their independent source/product audits are owned by `coupled_current_fresh/canonical_gm_independent`.
- `verify_source_root_euler.py` / results retain the explicit logarithmic term in the density Euler integral. They do not assert rational exactness.

Paths in this note are relative to `coupled-fresh/ruling-source/` unless an `audit/`, `endpoint/`, or `coupled-fresh/rank4-relative/` prefix is given relative to the packet root.

## Actual source and unresolved density correction

Put `J=j²`, `w=z²`, `T=1+w³`, and

```
N = 9 i² w² - 16 J T
M = 256 T⁵ N + 729 i⁶ J w⁶
P = 9 i² v M - 64 J w T² N = 0.
```

The chosen physical root gives

```
v = 64 J w T² N / (9 i² M)
hsrc = -3456 i³ v w² T³ / P_w
t = hsrc/(6v²) = -576 i³ w² T³/(v P_w)
a0 = 54 i³ w T/(j² N)
t v_w = a0/6.
```

All native derivatives below keep the other native variables fixed and differentiate the root using `w_p=-P_p/P_w`.

Let `V=6v∂v`, `D=V-2i∂i-j∂j`, and let `eb` denote the compact basis vector for `y`. The actual compact target is

```
t (4 eb - GammaD eb),   GammaD=GammaV-2i Gammai-j Gammaj.
```

Fresh found a polynomial compact eight-vector `U` with `nabla_j U=(4-GammaD)eb`:

```
U = [v(5j²-12i)/48, v(5j²-12i)/48, -1, 2,
     -5jv/24, jv(15j²-52i)/96, 0, -j/2].
```

Thus `Pj=tU` leaves the actual source `-t_j U`. This density derivative is **not zero** and remains unserved. The physical current `Pj=a0 U/6` instead leaves

```
-(a0_j U + a0 v_j nabla_v U)/6
```

in flat `(i,j,w)` volume, with the matching physical parameter/fiber currents. This is a rational, fold-free alternative to expanding native inverse-root derivatives, but it is not a completed closure.

Fresh's compact `Vi,W` obey

```
nabla_i Vi = U + j ebq/2,       nabla_j W = ebq.
```

The further currents `Pi=-t_j Vi`, `Pj=j t_j W/2` therefore leave

```
t_ij Vi - (t_j + j t_jj) W/2.
```

This is a genuine two-section compact density equation, retaining all eight components, not a scalar density integration result. All literal exact fiber potentials and Piola terms must accompany it.

For raw moments the native/D-normalized distinction is explicit:

```
Psi_j = y² dx/(2x⁴)
U1raw = -v y² dx/(x³ Jbar)
U1raw = (3-Dnative)Psi_j - d_x[y²/(2x³)]
partial_j[y²/(2x³)] = v x y/Jbar.
```

Dropping this exact term loses the source Cartan contribution.

## Last analytic density factors — not yet a standalone audited deliverable

The following formulas were derived algebraically in this agent's final analysis. They were sent to root/Fresh, but **no new dedicated verifier was run before the user stopped research**. They are recorded as derivations requiring a literal check before reuse.

`P` is quadratic in `J`, with coefficients

```
aJ = 1024 w T³
bJ = 9 i² [v(729 i⁶ w⁶ - 4096 T⁶) - 64 w³ T²]
cJ = 20736 i⁴ v T⁵ w².
```

For `W=w³`, its discriminant factors as

```
disc_J(P) = 81 i⁴ Dplus Dminus
Dplus/minus = v[27 i³ W +/- 64(1+W)³]² - 64 W(1+W)².
```

Each factor is generically a sextic in `W`, hence defines a genus-two curve. This does **not** identify either with the existing endpoint genus-two family or prove that the actual source descends to either factor.

At fixed `i,v`, the actual weighted differential is

```
t dj = 288 i³ w² T³/(v j P_J) dw
     = +/- 32 i T³/(3v j sqrt(Dplus Dminus)) dW.
```

The `1/j` factor and the cubic `w -> W` cover character remain. This differential is odd under `j -> -j`; therefore the discriminant factorization alone cannot be used to replace the actual source by a genus-two differential.

The earlier raw-pair finite-residue construction gives the exact candidate equation

```
(j/2) lambda_i + rho lambda_j = -t_ijj
rho = -1/2 + v(i-1/4)²(7/4-i)/48.
```

Since `t` is even in `j`, the parity-compatible substitution `lambda=j L(i,J,v,w)` yields

```
[(J/2) D_i + 2J rho D_J + rho] L = -2t_iJ - 4Jt_iJJ.
```

This is an exact rational equation in the degree-eighteen density-root field. No `L` or `lambda` was found. Its characteristic invariant is

```
j² + 2i - v(i-1/4)³(9/4-i)/48.
```

The resulting characteristic curve is generically elliptic; it must not be silently called the endpoint genus-two curve.

## Exact coordinate bridge to endpoint: source-retention gap

Use original quotient coordinates

```
a=x³, b=y³, q=xy, U=X2³, V=Y2³, p=X2 Y2,
ab=q³, UV=p³,
H=1+a²+b²+z⁶+zq/2, C=za/2+q/3,
Z=V²-U², Z²=(H+Cp)²-4p⁶.
```

Then

```
k=p/q
R=U²/a²=(-H-Cp-Z)/(2a²)
S=V²/b²=(-H-Cp+Z)*a²/(2q⁶)
Acoef=1+R, Bcoef=1+S
i=4k(1+z⁶)/(3z²)
j²=k²(1+z⁶)/Acoef
v=z⁶/[64(1+z⁶)⁴ Acoef Bcoef].
```

These rational expressions show the main gap: **the actual density and its compact moment coefficients depend on the endpoint fiber variables `p,Z`**, not only on endpoint base `H,C,z,a`. One cannot insert them as scalar base coefficients in the endpoint rank-four connection.

With `E=z/2`, `T=1+z⁶`, the full differential extension of the moment is

```
Psi_j = E² q²/[2T(a²+U²)] * d(Eq/T)
      = E³ q²/[2T²(a²+U²)] dq
        + E² q³/[2T(a²+U²)] d(E/T).
```

The base differential term must remain in a total current. The moving endpoint poles `a²+U²=0` must also be reduced with their residues; they are not captured merely by the compact rank-four basis.

Existing exact endpoint interfaces to use if this route resumes:

- `endpoint/CURRENT-INTERFACE.md` and `endpoint/reconstructed-connection.json`: compact basis `p^j dp/Z`, **j=0,1,3,4**, literal Dwork primitives and moving-pole connection. Keep both second-kind directions.
- `coupled-fresh/rank4-relative/SCALAR-HORIZONTAL-CLOSURE.md`: complete scalar horizontal equation `-L* f + T U + D_z W = sigma`, with actual `sigma=phi_H/6` (or its explicit shifted equivalent).
- `coupled-fresh/rank4-relative/BARE-FULL-HORIZONTAL-CLOSURE.md`: actual full-horizontal Bezout/current reduction, with the remaining compact equation explicit.
- `infinity-horizontal/BACKGROUND-ELLIPTIC-SOURCE.md` and the endpoint cubic-ray self-correspondence notes: retain the source kernel and both second-kind rows; neither universal traces nor background correspondences automatically recover this actual source.

No equality between the new density sextics, the old endpoint family, or their actual source-carrying currents has been proved. The final open task remains an exact weighted coupled current closing the actual density correction, including compact, finite-residue, infinity, and parameter terms.
