# Reflection-skew agent's completed cyclic audit index

This is a handoff index of existing receipts, not a solved target. All paths below are in `/workspace/research`. The exact cyclic source/certificate remains open. New research stopped at the user's instruction.

## Open-curve connection, polarization, and source conventions

- `round9/abel_prym/polarization.py`, `.pickle`, `.json`; `polarization_clean_frame.py`, `.pickle`, `.json`: exact 3x3 actual/conjugate cup product in the old and clean frames. All 27 pairing-flatness identities passed. The global common topological scalar is unspecified but constant. In the clean frame, pairing entry H[2,0]=7*x/18.
- `round9/abel_prym/rank5_ordinary_audit.py`, `.json`: 80 direct rational one-form derivative/primitive checks for all eight boundary rows. The PLUS primitive convention is `(QW-WQh)/(D*Ct)`.
- `round9/abel_prym/rank5_flatness_audit.py`, `.json`: all six full rank-five curvatures vanish exactly and all 16 quotient-block entries match the independent residue connection.
- `round9/abel_prym/open_frame_audit.py`, `.json`: exact rational residue frame and third-kind projection. In the frame sigma_j=W^(3j)dW/[(T-s)Ct], residues are -w^(3j)/CW. Infinity orders are 4 and 1.
- `round9/abel_prym/higher_pole_audit.py`, `.json`: direct moving-curve pole-two identities, with PLUS primitive including the full derivative of `(QW-WQh)/Ct`; no missing factor two.
- `round9/abel_prym/hodge_pairing_nullflow.py`, `.json`: exact marked Abel-Prym/Hodge coupling on the Prym-nullflow plus arbitrary moving-mark direction. It includes all absolute Q8 corrections and the scalar -1/6 against the corrected marked conjugate form.
- `round9/abel_prym/hodge_pairing_fullbase.py`: only the s direction finished before a 90-second symbolic cap. There is no full-base receipt or claim.
- `round9/abel_prym/nullflow_completion_audit.py`, `.json`: independently reproduced four nonzero third-jet compatibility defects. Scope: the restricted boundary current carrying the entire eta source along the nullflow with eta-free proper corrections. This does not exclude general rank-five currents.

Assembly inputs by other agents: `round9/open_curve/boundary_native.pickle` (off's exact boundary rows/primitive coefficients), `round10/horizontal5/rank5_connection.pickle` (cert's full connection), and `round10/horizontal5/physical_search.py` (effective-mark physical pullback).

## Canonical cone and global adjoints

- `round9/abel_prym/canonical_cone_audit.py`, `.json`: the generic common-zero cone is the canonical genus-four CI(2,3), with exact character shifts. Local R1O character counts are (1,1,3), not the unshifted counts. This is local data, not a global H20 result.
- `round9/abel_prym/global_adjoint_map.txt`: finite-flat physical order, character line bundles, adjoint map, and scope. Its raw H1 and H2 vanish, but normalization/resolution conditions are separate.
- `round10/horizontal5/global_twists/compute.py`, `global_cone_twists.json`, `README.md` (cert's independent check): physical M=(15,17), F=(0,1), T=(-2,2), canonical line (42,54). For the full common-zero CI, K_Z=(25,34). Relevant graded R1 lines are (-17,-20),(-2,-3),(-4,-1). Twisted J^2 Koszul gives cone-only jet restriction surjectivity. Additional conductor/corner adjoints can restrict the domain and were not disposed of by this calculation.

## Generic conductor repair and vertex models

- `round9/abel_prym/conductor_tangent.py`, `.json`: exact split transverse node and its degree-23 common tangent factor. Removing that factor cannot justify an O(-7) global conductor by itself.
- `round9/abel_prym/conductor_intermediate_order.txt`: global union conductor repair for S=Y0^6+Y2^6, b=Y1 and D=qS^2+brS+b^2s. The integral theta=qS/b satisfies theta^2+r theta+qs=0. The intermediate quotient is O_T(-25), T=(b,S), and its generic repair adds neither H1 nor H2 because T is ACM and canonical restriction interpolates. This does not include every separate boundary or resolution defect.
- `round9/abel_prym/corner_CI_audit.py`, `.json`: exact generic weighted ICIS audit at the six ruled-surface vertices. Weights (eps,W,b,r)=(3,2,6,6), equations degree 12, a-invariant7. Quasismoothness checked over both cyclotomic components at a good v; low-weight local adjoint quotient dimension10, characters (2,2,6). Extending this local calculation globally requires the special-v/collision audits owned by fresh/cert/rank.
- `round9/abel_prym/vertex_global_jet_sections.py`, `.json`, `.pickle`: explicit degree-32 preimages of all 420 generic Y-even/chi1 vertex jets, and the relevant 140 after the fine diagonal-character screen. These sections satisfy the generic union-conductor condition; additional boundary/corner conditions can still restrict them.
- `round10/horizontal5/global_boundary/source_transition.py`, `.json` (cert): actual pulled source and exact v-transition. The canonical frame transforms by -v^16, actual Y-even slots are 1,eps^2,b,r, and fine target diagonal character selects 140 directions.

Crucial source caveat: the actual pole-two source has a lower-weight deformation F_lambda=F+lambda*eps^3*a^3; its pulled density contains -eps^4*b/(6a^2). A bare weighted numerator cutoff is not an identified Gysin/duality map. Neither the local pg count nor generic adjoint interpolation establishes zero or nonzero actual source projection.

## Bounded searches retained with narrow scope

`round9/abel_prym/full24_constant.json`, `full24_correction.json`, `full24_z_correction.json` report finite-prime ranks 144/145,144/145,288/289 for the specified old-mark trace-current modules. They do not exclude other currents or supports. Independent old-mark fields/derivatives replayed in `independent_trace_audit.json`. The old graph's fixed-part audit (`independent_G_fixed_part.json`) excludes a flat holomorphic line/constant E0 summand along generic b in that specific support, not every H20 class.
