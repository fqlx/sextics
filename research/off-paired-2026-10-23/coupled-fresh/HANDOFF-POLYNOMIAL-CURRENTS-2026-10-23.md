# Polynomial compact currents: frozen handoff

Research stopped at the user's request on 2026-10-23. **No rational primitive/certificate for the immutable sextic has been obtained.** All results below are constructive partial currents; their displayed residuals remain obligations. No repository or external-service write was made by this workstream.

## Authoritative coordinates and connection

Use native base `(i,j,v)`, curve `ay=x^3`,

`y^2+v(a^2+i*x^2+j*a*x+x+1)=0`,

`Jbar=v(2a^2+j*a*x)-2y^2`, `nu_N=v*N*dx/Jbar`.

The compact basis is `[1,x,x^3,x^4-v(i-j^2/4)(i-5j^2/4)x^2/8,a,ax+jx^2/2,y,yx]`; `e_b=e6`, `e_bq=e7` use zero-based indices. The ninth stored connection row is the infinity form `omega=nu_(x^2)` and is retained in every generic check. Connection columns differentiate basis forms, with the stored rational fiber primitives retained.

`V=6v partial_v`, `D=V-2i partial_i-j partial_j`. Physical coordinates are `(i,j,w)`, with

`T=1+w^3`, `N=9i^2w^2-16j^2T`, `L=256T^5N+729i^6j^2w^6`,

`v=64j^2wNT^2/(9i^2L)`.

Authoritative connection/source files:

- `ruling-source/full-base-connection/rank8-ij-connections-results.json`
- `ruling-source/full-base-connection/rank8-v-literal-primitives-results.json`
- `ruling-source/full-base-connection/source-euler-current-results.json`
- `ruling-source/full-base-connection/FULL-BASE-COMPACT-PDE.md`

The Euler-reduced actual source is `t Q`, where `Q=(4I-Gamma_D)e_b`, `t=hsrc/(6v^2)`. In physical volume `di dj dw` it is `a0 Q/6`, where `a0=54i^3wT/(j^2N)` and `v_w*t=a0/6`.

## Verified compact j primitive and its exact residual

`Psi_j=y^2 dx/(2x^4)` satisfies `partial_j Psi_j=nu_b` literally. Its full compact/infinity/fiber reduction gives the polynomial compact vector

`U=[v(5j^2-12i)/48,v(5j^2-12i)/48,-1,2,-5jv/24,jv(15j^2-52i)/96,0,-j/2]`.

The complete generic identity is `nabla_j U=Q`. Thus the native current `P_j=t U` serves the source and leaves **`-t_j U`**, with the derivative taken at fixed `(i,v)` and all inverse-branch derivatives retained. Its literal fiber current is `-t*(fiberprimitive_j dot U)*di dj dv`. The direct original source includes the additional, already fixed Cartan term described below.

For physical volume the Piola current is `P_j=v_w*t U`, `P_w=-v_j*t U`, `P_i=0`; its residual is `-v_w*t_j U`. Alternatively, using only the fixed-w current `P_j=a0 U/6` leaves exactly `-[a0_j U+a0 v_j nabla_v U]/6`; it is fold-free but has the full connection term.

Files: `ruling-source/full-base-connection/build_j_source_primitive.py` and `j-source-primitive-results.json`. The latest producer passes **33 exact generic groups**, including all nine source-identity rows, literal curve reduction, infinity cancellation, and the second primitive below. Independent source audit passed **45 groups**: `audit/theta/j-source-current-audit-results.json`.

## Second compact primitive and the two-section residual

The same JSON stores

`W=[-5v(4i-j^2)/48,-v(16i^2+12i-5j^2)/48,3,2,-jv(4i+5)/24,-jv(52i-15j^2)/96,0,2j]`,

with **`nabla_j W=e_bq`** in all nine generic rows. A literal residue-free representative is

`beta7=y^2 dx/(2x^3)+(vi/2)(dlog x-dlog y/3)`.

These are rational logarithmic differentials, not an instruction to adjoin logarithmic functions. Its exact rational fiber primitive `G7` and derivative correction are stored.

The compact mixed section `Vi` is authoritative in `theta-compact/mixed-i-primitive-results.json`. It satisfies `nabla_i Vi=U+(j/2)e_bq`. Consequently, after the j current above, the additional native currents

`P_i=-t_j Vi`, `P_j+=(j*t_j/2) W`

leave exactly **`t_ij Vi-(t_j+j*t_jj)W/2`**. This retains all eight compact components and all physical density derivatives. It does not solve the sextic primitive problem.

Additional exact polynomial identities are

`nabla_i W=-v(e0+2i e1+j e4)/6`,

`nabla_V W=6W-6e2-3j e7`,

`nabla_j Vi=Ui+(j/2)e2`, `nabla_V Vi=6Vi+6e1-(3j/2)e_b`,

where `Ui=[0,0,j/6,0,0,0,2/3,i/3]` and `nabla_i Ui=Q+e7/2`.

Independent child verification: `genus4-gm-independent/verify_full_base_polynomial_potentials.py` and `full-base-polynomial-potential-audit.json`, **54 generic full-nine-row identities plus 3 unrestricted product-rule checks**, SHA256 `725039e7ecc78be0b338c4cceef22a7ca268ad0bcfd6fcfe656518750c976abc`. Exploratory contractions are preserved in `ruling-source/full-base-connection/polynomial-potential-rows-results.json`; they are not a certificate or a completed density solve.

The child's stopped-work handoff is `genus4-gm-independent/HANDOFF-POLYNOMIAL-POTENTIALS.md`. It also records the algebraic consequence

`e_b=(3/2)nabla_j Vi+(j/6)nabla_V W+((j^2-i)/2)nabla_j W-jW`.

For the original native source `g e_b`, `g=(D-5)hsrc/(6v^2)`, this gives the direct current `P_j=(3/2)g Vi+((j^2-i)/2)g W`, `P_v=jvg W`, and exact remaining source

`-(3/2)g_j Vi-[jv g_v+((j^2-i)/2)g_j+3jg]W`.

This direct formula is algebraically derived from the verified packet; no separate post-stop executable check was run. It remains a partial current with the displayed actual density residual.

## Essential Cartan/fiber convention

Do not confuse native `D` with `Dnorm=D+Lie_(x partial_x)` on relative forms. The literal normalized primitive

`U1raw=-v*y^2 dx/(x^3 Jbar)`

satisfies

`U1raw=(3-D)Psi_j-d_x[y^2/(2x^3)]`.

In particular `partial_j[y^2/(2x^3)]=v*x*y/Jbar`. The direct pre-j fiber current is therefore `-t*(fD_b+v*x*y/Jbar)*di dj dv`, with signs already communicated to the independent ambient-pullback auditor. Dropping this exact Cartan correction corrupts the literal original-source current even though compact cohomology agrees.

## Other source-bound progress and next step

The separate theta/quartic workstream produced a fixed-w weighted current `P_j=c e_bq`, `c=-iT/(4wj)+28T^2j/(45iw^3)`, which serves the original `N=0` and `j=0` source poles. Its full remaining eight-vector source and all `v_j` terms are authoritative in `theta-compact/actual-N-j-removed-source-results.json` (22 exact groups); it is still open. Ruling owns the actual density/endpoint bridge, theta the weighted source reduction, and the source auditor the original ambient pullback. A useful restart should solve one of these **actual** residuals while retaining fiber and all second-kind/infinity corrections, then verify the reconstructed divergence in the original immutable sextic coordinates.

The older exact scalar `K` construction remains valid but leaves its full curve/kernel correction. Key entry points are `ruling-source/adjoint-reconstruction/N-ONLY-RATIONAL-LIFT.md` and `genus4-gm-independent/ACTUAL-RATIONAL-K.md`; these are not primitive certificates. Full cubic-moment properization can raise the Morse pole order of `K/v` to five, so the safe quartic-source fold bound is four/current denominator `Ccrit^3`. The core source route above no longer requires expanding that construction.

Run FLINT scripts with `/workspace/tooling/sextics-venv/bin/python`; the default Python lacks python-flint. No additional computation is needed to freeze this handoff.
