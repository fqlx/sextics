# Frozen handoff — generic compact connection and actual N/j current

Frozen on 2026-10-23 after the user stopped research. No new solve is proposed
here. **The immutable sextic remains unsolved:** no full source primitive,
certificate, Lean proof, local kernel verification, solve PR, protected CI or
acceptance exists.

## Concise claims suitable for publication

1. An explicit rational **rank-eight compact Gauss–Manin connection** is
   available on the genus-four family
   `ay=x³, y²+v(a²+i x²+jax+x+1)=0`, in all three base directions `i,j,v`.
   Every rational fiber-exact term is recorded. The primary generic V solve
   checks 333 cleared polynomial coefficients; the additional c,d solve
   checks 666. Independent audits pass **82** generic compact/deck groups and
   **886** full-base/literal-primitive/flatness groups. These are exact local
   algebra computations, not Lean or kernel verification.
2. The actual source, after its explicit first full-base Euler current,
   retains the nonzero compact eight-vector
   `S=9i³wT/(j²N) Q`, with `Q=(4−GammaD)e_b`,
   `GammaD=GammaV−2i Gamma_i−j Gamma_j`, and volume `di∧dj∧dw`.
   Its independent exact Euler-current audit passes **32** groups. This is a
   source-carrying partial current, not source closure.
3. The explicit fixed-w j current
   `Pj=[−iT/(4wj)+28T²j/(45iw³)]e_bq`, `Pi=Pw=0`, removes the
   original **N and j=0 poles**. Its complete retained eight-vector is saved;
   it has no N, j or critical-v_w denominator. The verification passes **22**
   exact groups: sixteen vector divisibility checks and six scalar/transport
   identities, combined with the audited full connection. Do not describe
   this as a separately rerun large ambient six-variable identity.

The compact basis is

    nu = v*[1,x,x³,x⁴−v*r*x²,a,ax+j*x²/2,y,yx] dx/Jbar,
    r=(i−j²/4)*(i−5j²/4)/8,
    Jbar=2va²+jvax−2y².

Matrix columns differentiate basis forms. Coefficient currents therefore use
`partial_p P+Gamma_p P`, including their stored fiber-exact corrections.
The zero-based `e_b` index is 6 and `e_bq` index is 7. In physical `(i,j,w)`
coordinates the j connection is `Gamma_j+(v_j/(6v))*GammaV` and the w
connection is `v_w*GammaV/(6v)`; freezing v or dropping these chain terms is
incorrect.

## Exact current remainder

Use

    T=1+w³,
    N=9i²w²−16j²T,
    L=256T⁵N+729i⁶j²w⁶,
    v=64j²wNT²/(9i²L).

`actual-N-j-removed-source-results.json` is the authoritative packet for
this stage. It records

    R=64iw²T³/L * B − cv*J − dv*H + e*e_bq,
    B=(Q+GammaV*e_bq/30)/v,
    H=(GammaV*e_bq−5e_bq)/v,
    J=Gamma_j*e_bq/v.

Each vector's numerator is exactly divisible by v. Their common curve
discriminant denominator `D(i,j,v)` and all scalar coefficients are stored.
The remaining explicit pole set is **i=0, w=0, L=0 and D(v(w))=0**, including
intersections. This full remainder is nonzero and unserved.

A subsequent partial joint w/j current is frozen separately at
`../quartic-kernel/W0-JOINT-CURRENT-HANDOFF.md` and
`../quartic-kernel/w0-joint-current-results.json`. Its added coefficients are

    deltaPj=−224j(2−w³)/(405iw³)*e_bq,
    deltaPw=−448T/(405iw²)*e_bq.

It removes the leading order-three w=0 term while preserving the served
N/j/T profiles. Its lower w=0 jets remain open. The elementary identities
were checked; the large eight-vector identity was not independently rerun
after this last addition. If reporting the latest stage, its remainder is
`R−nabla_j(deltaPj)−nabla_w(deltaPw)`, with every fiber term retained.

## Reproduction: existing frozen arrays

Tested local runtime: Python **3.11.17**, SymPy **1.14.0**, python-flint
**0.9.0**. The prepared executable is
`/workspace/tooling/sextics-venv/bin/python`. No NumPy, Sage, Lean, network,
credentials or original Mac paths are needed for the following local checks.
Run from the packet root `/workspace/off-paired-research-new`:

```sh
/workspace/tooling/sextics-venv/bin/python audit/theta/verify_generic_compact_connection.py
/workspace/tooling/sextics-venv/bin/python audit/theta/verify_full_base_connection.py
/workspace/tooling/sextics-venv/bin/python audit/theta/verify_source_euler_current.py
/workspace/tooling/sextics-venv/bin/python coupled-fresh/theta-compact/remove_actual_N_pole.py
/workspace/tooling/sextics-venv/bin/python coupled-fresh/theta-compact/remove_actual_N_j_poles.py
```

All five commands were rerun successfully for this handoff: 82, 886, 32,
11 and 22 checks respectively. The audit scripts reconstruct the implicit
curve identities independently of the primary connection solver.

Required frozen results for these commands:

- `theta-compact/affine-V-generic-results.json`,
  `rank8-descended-connection-results.json`,
  `actual-N-removed-source-results.json`.
- `ruling-source/full-base-connection/affine-cd-generic-results.json`,
  `rank8-ij-connections-results.json`,
  `rank8-v-literal-primitives-results.json`,
  `source-euler-current-results.json`.
- `audit/theta/verify_generic_compact_connection.py`, imported by the
  independent full-base auditor; preserve the sibling packet layout.

The three audit outputs are `generic-compact-connection-audit-results.json`,
`full-base-connection-audit-results.json`, and
`source-euler-current-audit-results.json` in `audit/theta/`.
The pole-current outputs are `actual-N-removed-source-results.json` and
`actual-N-j-removed-source-results.json` here. Scripts write JSON next to
themselves. The Euler source packet currently keys its connection-input hashes
by absolute resolved paths. If the packet is moved, rebuild
`build_source_euler_current.py` before its audit so those keys match the new
location. Rebuilding arrays may also change runtime fields and hashes; run
independent audits after builders to rebind the recorded source hashes.

## Regenerating connection arrays

Preserve `affine-e-connection-results.json` (selected polynomial chart),
`core-checkpoint-V.json` (the exact eight-dimensional core), and sibling
`affine_e_connection.py` / `affine_theta_reduction.py`. Then run, in order:

```sh
/workspace/tooling/sextics-venv/bin/python coupled-fresh/theta-compact/finalize_generic_flint.py
/workspace/tooling/sextics-venv/bin/python coupled-fresh/theta-compact/descend_connection_flint.py
/workspace/tooling/sextics-venv/bin/python coupled-fresh/ruling-source/full-base-connection/build_affine_cd_flint.py
/workspace/tooling/sextics-venv/bin/python coupled-fresh/ruling-source/full-base-connection/descend_ij_connections_flint.py
/workspace/tooling/sextics-venv/bin/python coupled-fresh/ruling-source/full-base-connection/descend_v_primitives_flint.py
/workspace/tooling/sextics-venv/bin/python coupled-fresh/ruling-source/full-base-connection/build_source_euler_current.py
```

The subsequent five audit/current commands above complete this reproduction
chain. The saved core is fully checked against all original generic curve
coefficients by the first builder; it is not trusted solely as a numerical
specialization. `solve_affine_connection_fast.py V` can regenerate the core,
but its later SymPy canonicalization is slow; the native FLINT finalizer is
the preferred saved-core path. `expand_affine_e_connection.py` and
`connection_local_exponents.py` are obsolete exploratory paths, not required
reproduction commands.

## Other saved work: preserve its scope

- `mixed-i-primitive-results.json`: explicit compact `Vi` with
  `nabla_i Vi=U1+(j/2)nu_bq`; all eight generic identities pass. Weighted
  use retains the density corrections `t_ij Vi+(j/2)t_j nu_bq`.
- `source-leray-presentation-results.json`: full actual residual arrays
  after a known infinity current and a factored **848×80** logarithmic
  w-complex presentation. It is not an expanded reduced cokernel basis or
  a solved induced horizontal system. Its builder is
  `construct_leray_presentation.py` and imports the native Laurent
  arithmetic in `construct_source_taylor_current.py`.
- `discriminant-normal-residue-results.json`: 128 exact normal residue
  entries. `discriminant-normal-inverse-results.json`: an exact inverse of
  D_i modulo D via a seven by seven Sylvester calculation. Neither file
  supplies a physical discriminant-serving current or serves the poles
  such a current would introduce.
- The Taylor feedback JSON files are exploratory restricted relative-w
  feedback, not a global obstruction or a publication substitute for
  source closure. Do not promote them to a full nonexistence result.

No external write was performed by this agent.
