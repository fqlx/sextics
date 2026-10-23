# Source-bound open-curve extension for cyclic-triple-residual

This folder implements a concrete new current channel; it is not a certificate.

The proper actual-character basis is the clean polynomial frame from `/workspace/research/round9/cyclic_full/global_eta_complete.pickle`. Add the two simple marked-divisor forms

    sigma0 = Res[h4*Omega/((t-s*h²)*C)],
    sigma1 = Res[W³h*Omega/((t-s*h²)*C)].

Their six-point residue quotient has actual-character dimension2, so the full open connection has rank5. These boundary classes retain the H0(marked points)(-1) extension absent from the proper rank3 connection.

## Exact universal connection

`export_linear_packet.py` constructs the common-D²C² homogeneous coefficient system:19 invariant weight12 monomials,5 cohomology columns,16 primitive columns. Its rank is17, with four Euler primitive gauges. `native_solve.py` solves all8 boundary derivative rows at once over QQ(L,r,x,s), using native FLINT rational arithmetic and small-complexity pivots. It verifies every solution against all19 universal coefficient equations exactly. Runtime was1.25s. The slower generic SymPy inverse was stopped and superseded; no mathematical conclusion depends on the interrupted run.

`boundary_native.pickle` contains:

- variables `(L,r,x,s)`;
- `connection_boundary[direction]`: two rows, five entries each;
- `primitive_coefficients[direction]`: two rows,16 entries each;
- `primitive_labels`: component and `(W,h,t)` monomial for each primitive coefficient.

Every rational entry is a pair of numerator/denominator coefficient dictionaries. The first3 connection columns use the literal clean eta_new frame; the last2 use sigma0,sigma1. The primitive is `i_Q Omega/(D*C)` and its affine residue has the independently fixed plus sign `(QW-W*Qh)/(D*Ct)`.

Certificate_search assembled all5 rows and verified all6 rational curvature pairs exactly in `/workspace/research/round10/horizontal5/rank5_connection.pickle/json`, including agreement with the independently derived2×2 residue block. Poles are simple along the expected x,D1,D2,B,Delta. Reflection independently checked the ordinary1form reductions, all5 curvature, residue quotient, and theta normalization. My separate finite-prime jet audit in `flatness_point_audit.py/json` passes1800 entries at12 points; it is a supplemental finite audit, not the exact-flatness proof.

## Compact source/Hodge coupling

`hodge_leading.py` exports all boundary-to-eta1forms. `vertical_hodge.py` proves the compact contraction along the pinned Prym-isoperiodic vector field delta. Set

    A=c*(1+s), B=L+r*s+s³/x, Delta=A²-4B,
    K=r*(5s+4)+3s*(2s+3)/x, c=5/7.

Then

    E_s=(A,-2B)/(7*x*B*Delta),
    E_delta=x*K*E_s+c*(-2,A)/(7*Delta).

For a moving graph s=e, add delta(e)*E_s. All D1,D2 factors cancel in this vertical contraction. With u=w³, u²+A*u+B=0 and the horizontal residue coefficient vector f=w²*(-A-u,-1),

    f.E=[delta(e)/x+K+c*u]/[7*w*(2u+A)].

These identities are exact. Reflection's literal primitive/polarization audit further gives `<eta_new, conjugate hol>=7x/18` and the corresponding corrected marked Abel differential; receipt `/workspace/research/round9/abel_prym/hodge_pairing_nullflow.json`.

## Two limited nullflow trials

Let S_eta be the actual source's clean eta coefficient and e the source-specific effective graph. Put D0=delta(e)/x+K and NF=D0²-c*A*D0+c²B. The rational quadratic-trace seed

    Z=-7*S_eta*Delta/(2*NF)*(c*B,D0)

satisfies the eta source equation exactly. `forced_nullflow.py/json` retains all physical first/second jets and shows that this seed has nonzero residue-closedness defect at four good points.

`nullflow_completion.py/json` adds the entire eta-orthogonal direction T*P, P=(B*(2D0-cA), A*D0-2cB). The two residue-closure equations force T and delta(T). Exact third formal trajectories of the canonical nullflow, inverted coefficientwise through the physical parameter map, show a nonzero derivative-compatibility defect at the same four points. This is a narrow restriction: boundary current along delta only, carrying the entire eta source, with proper corrections eta-free. It does not exclude transverse boundary2forms, proper holomorphic currents contributing eta, or general rank5 currents. An independent jet audit has been requested.

## Current constructive direction

The physical effective graph has a nonrational canonical genus4 cone along its pencil base curve N0p=N1p=0. A boundary2form with a nonzero holomorphic restriction on the exceptional surface requires an explicit N0p^-2 radial amplitude. The exact physical normal frame and first jets are implemented separately in `/workspace/research/round10/cone_radial/frame.py`, with canceled physical N0p,N1p normalization and holdouts. Certificate_search owns the radial current module; Fresh owns cone geometry and residue-closed2form families; rank_candidates independently audits the new frame. No source-serving Gysin class or primitive has been obtained yet.
