# Horizontal marked-divisor extension

This packet adds the horizontal support sector missing from the proper
rank-three PDE. The universal rank-five connection, its exact flatness,
residue normalization, and physical source pullback are implemented and
audited. No primitive or accepted certificate has been found.

The canonical curve is
`C=W^6+(5/7)(h^3+h*t)W^3+L*h^6+r*h^4*t+t^3/x`.
Use the clean proper basis from `round9/cyclic_full/global_eta_frame.pickle`
and the additional graph-pole forms

```
sigma0 = Res(h^4 Omega/((t-s*h^2)*C)),
sigma1 = Res(W^3*h Omega/((t-s*h^2)*C)).
```

On h=1 these are `dW/((t-s)Ct)` and `W^3 dW/((t-s)Ct)`.
Their six residues are `r0=-1/CW,r1=-W^3/CW`. Both forms have no infinity
poles (orders four and one). The rank-three proper derivatives occupy the
upper-left block and have zero boundary components; the two extra rows
were reduced independently by off_paired in
`/workspace/research/round9/open_curve/boundary_native.pickle`.
All eight weighted polynomial reduction identities and exact primitives
are retained there. Those primitives use PLUS
`(Q_W-W*Q_h)/((t-s)*Ct)` on h=1.

`assemble.py` combines the blocks, verifies every bottom-right entry against
an independent finite-point residue computation, saves the matrix before
expensive checks, and verifies all six curvature matrices exactly over
QQ(L,r,x,s). `rank5_connection.pickle/json` record the result and SHA256-bound
inputs. Full exact flatness took 1.23 seconds. Matrix denominators are simple
factors only: x, D1, D2, `P=L*x+r*x*s+s^3`, and
`Q=196Lx+196rxs-25xs^2-50xs-25x+196s^3` (up to signs/scalars).

The convention is row basis:
`partial_j beta_i=sum_k N_j[i,k] beta_k + fiber-exact`.
Coefficient columns use `partial_j+N_j^T`, and curvature is
`partial_i N_j-partial_j N_i+N_j*N_i-N_i*N_j`.

`residue_connection.py` independently computes the rank-two residue block
in `u=W^3`, `u^2+q*u+p=0`, with q=(5/7)(1+s), p=L+rs+s³/x.
It also verifies all four horizontal coefficient identities for the exact
third-kind character projection

```
theta_chi=(1-zeta3^2)*w^2*((-q-u)*sigma0-sigma1).
```

Thus its proper derivative is
`(1-zeta3^2)*w^2*((-q-u)*N_j[3,0:3]-N_j[4,0:3])`.
Reflection independently verified the same normalization, every residue
entry, and full exact flatness; independent receipts are
`round9/abel_prym/{open_frame_audit,rank5_flatness_audit}.py/json`.
The independent ordinary moving-curve derivative audit also passed all eight
boundary rows and primitive signs at multiple finite-field points:
`round9/abel_prym/rank5_ordinary_audit.py/json`.

## Physical source and currents

`physical_search.py` pulls the universal system to (a,b,v), setting
`s=Teff=N1/N0` from the source-bound Higgs kernel in
`round9/abel_prym/effective_schiffer.pickle`. The actual source still embeds
in the first three coordinates, with zero last two coordinates. Its source
mark z=BR/A is distinct from the horizontal graph mark s.
All derivatives of s are retained. At every point the universal chain-rule
value and all three derivatives agree with the separately canceled physical
rational expression in `effective_physical.pickle`.

For physical currents the operator includes the full logarithmic density
`dlog(rho*fT)=3da/a+(2/3)dS/S-3db/b-3dE/E-(2/3)dAphys/Aphys`,
where rho³=Aphys/(3S), fT=3a³S/(2B³Aphys). Both raw-rho and rho*fT densities
are available. Boundary output equations impose residue-current closedness;
proper output equations retain the source and extension couplings.

Initial exact finite-prime screens only reject their displayed finite modules:
constant all-five-component currents have rank30/aug31; degree-two physical
currents plus the known first-current residual have300/301. A completed
bounded both-frame degree-two module with source-mark and graph-mark factors
has2400/2401. These do not exclude the unrestricted horizontal route.

## Structured marked-log currents

The independent complete free logarithmic module is
`round9/marked_log_module/verified.pickle`. It has four universal polynomial
fields W_i tangent to x*D1*D2*P*Q, and every full rank-five contraction N(W_i)
is polynomial. On the physical graph the normal defects are
`psi_i=W_i(s)-sum_j W_i(j)*V_j(Teff)`.

`log_search.py` forms six tangent combinations
`T_ij=psi_j*W_i-psi_i*W_j`. `jet2.py` retains actual second derivatives in all
three physical variables, including derivatives of the defects and inverse
Jacobian. The connection contraction is
`psi_j*N(W_i)-psi_i*N(W_j)`; all N_s correction terms cancel. Each sampled
point checks the differentiated inverse-Jacobian identity, tangent identity,
and every one of the 25 connection contraction entries for all six fields.
`log_fields_holdouts.json` exports values, derivatives, divergences, and
contractions at three points for a fully independent jet audit.
The constant unscaled marked-log module has rank60/aug61 modulo1000003.
No larger generic proper-current sweep is active; constructive source-matched
boundary seeds and non-exact residue classes are being investigated separately.

The fully independent physical jet audit
`round9/marked_log_module/physical.py` and `physical_audit.json` uses a distinct
Taylor-coefficient implementation and an independently reduced eta1/eta0
Schiffer ratio. It matches all three holdouts, all defects/gradients, every
pair field/full gradient/divergence, and all 25 connection contractions.
Normalized chart-field constant modules are documented by that independent
runner; their bounded negative results do not exclude the marked-log route.

`closed_seed_search.py` adds twelve exactly residue-closed current columns
from `fresh/physical_candidates.py` to a small proper marked-log module.
Closure is independently rechecked against the assembled rank-five residue
block at every point, including rho and fT twists. These are exact residue
classes with explicit one-form potentials, so their proper images are
preconditioners rather than evidence of new Gysin classes. The initial
156-column module has rank156/aug157 modulo1000003.

All search JSON/pickle files save arguments, exact modular ranks, sample
points, and column labels. A sampled positive would require fresh-point
verification and QQ reconstruction before any certificate claim. All files
are scratch research outside the protected repository.
