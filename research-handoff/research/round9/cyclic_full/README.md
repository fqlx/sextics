# Full transverse Prym connection for cyclic-triple-residual

The actual source-compatible rank-three Gauss--Manin system has been computed
and audited. No primitive, accepted certificate, or solved open target is
asserted. The new full transverse system is not the one-direction scalar
projection excluded in round8.

The canonical weighted curve is
`C=W^6+(5/7)(h^3+h*t)W^3+L*h^6+r*h^4*t+t^3/x`.
`actual_fast.pickle` has actual-character basis
`(h^2 Omega/C,t Omega/C,t^4 Omega/C^2)` and all three connection matrices.
`conjugate_fast.pickle` has basis
`(W*h Omega/C,W*h*t^3 Omega/C^2,W*h^3*t^2 Omega/C^2)`.
The row convention is `partial_j beta_i=sum_k N_j[i,k] beta_k + fiber-exact`.
Coefficient columns therefore use `partial_j+N_j^T`.

`fast_connection.py` computes exact polynomial coefficient-vector Griffiths
reductions over QQ(L,r,x), including all fiber-exact corrections. Common
denominators are stored separately to avoid expression growth. Every defining
Jacobian identity was checked exactly. The raw primitive schema is
`Q8_raw/Q8_denominator` over `lab8`, and, for pole-three intermediate terms,
`Q14_raw/Q14_denominator` over the selected `lab14`.

`audit_flatness.py` verifies all six curvature matrices identically using
native rational multivariate arithmetic; `flatness_audit.json` records the
result. With row convention the curvature is
`partial_i N_j-partial_j N_i+N_j*N_i-N_i*N_j`.
The independent parent replay is
`independent_flatness_jets.py/json`: numerator/denominator first jets at
25 random points for each of the actual/conjugate systems, SHA256-bound.
The actual source identity `Res(h^4*t^2 Omega/C^2)=-nabla_r omega1`
and both existing isoperiodic-flow handoff matrices agree exactly.

`independent_physical_source.py/json` separately reads the pinned original
sextic and verifies the literal source substitution and its positive affine
Jacobian. The physical source/current normalization is documented in
`/workspace/research/round8/coupled_source/README.md`. The finite coupled
current searches and their independent evaluator audit are indexed in
`/workspace/research/round9/coupled_search/README.md`.

The geometric singular loci on the affine parameter chart are `x=0`,
`D1=27L^2+4r^3*x=0`, and `D2=0`, where D2 is the discriminant of the
elliptic quotient cubic, up to a nonzero scalar. `elliptic_log_fields.pickle`
contains three exact polynomial D2-logarithmic vector fields; their determinant
is a unit times x*D2. The larger common denominator HolD of the initial hol
connection rows is an apparent selected-frame factor, not an extra curve
discriminant. Its physical pullback factorization is recorded algebraically
in `../coupled_search/gm_pullback_factors_QQ.pickle`.

`theta_frame.py/json/pickle` changes the third basis vector to
`theta=nabla_r omega0`, checks every gauge identity exactly, and removes HolD
in favor of a lower-degree apparent factor K. This is a different rational
frame for the same rank-three system, not an enlarged cohomology space.

`full_connection.py` and `actual_connection.py` are earlier abandoned
expression-growth implementations. Use the `*_fast.pickle` files above;
the earlier partial logs do not claim completed matrices. All files are
scratch research outside the protected repository.
