# Coupled physical-base current search

This is the first full transverse rank-three PDE search for the actual
`cyclic-triple-residual` source. All coefficient derivatives, cubic-root
character, source weights, and physical Jacobian terms are retained.
No primitive or certificate was found in the finite modules below. These
results do not exclude the unrestricted coupled PDE or the open target.

The exact source and base map are documented in
`/workspace/research/round8/coupled_source/README.md`; the verified connection
is in `../cyclic_full/actual_fast.pickle`. Write z=BR/A,
fT=3a^3*S/(2B^3*A), rho^3=A/(3S), and J=det d(L,r,x)/d(a,b,v).
For canonical coordinate fields pulled back to the physical base,

```
sum_j [ V_j Z_j + N_j^T Z_j + (V_j log H) Z_j ]
 = -N_r^T e1 + 2z N_r^T e0 - z^2 N_L^T e0,
H=rho*fT/J.
```

The logarithmic covector is
`3da/a+(13/3)dA/A-5db/b-4dE/E-(4/3)dS/S-dDelta47/Delta47`.
The equivalent physical-coordinate frame has connection
`sum_j (partial_i param_j) N_j` and logarithmic weight
`dlog(rho*fT)=3da/a+(2/3)dS/S-3db/b-3dE/E-(2/3)dA/A`.
The fixed first integration-by-parts current is
`Z_r=-e1+2z e0,Z_L=-z^2 e0,Z_x=0`; its remaining source is exactly
`(-2V_r z-2z phi_r+2z V_L z+z^2 phi_L,phi_r,0)`.

`search.py` uses exact first jets modulo a prime, inverts the physical
Jacobian, evaluates all three verified GM matrices, and builds finite
current modules. Every sample checks field duality, exact factored Jacobian,
and full source minus the first current against the pure holomorphic residual.
Features are `{1,z,z^2}` times physical monomials of the specified total degree;
`eta` gives the degree bound for the third component. The theta option uses
the independently verified third vector theta=nabla_r omega0 instead.

`higgs_search.py` uses five rational holomorphic current generators. For
each `(j,c)!=(x,omega1)`, put `q=-x^2*N_j[c,2]` and take omega_c along j
plus q*omega1 along x. Because `N_x[omega1,:]=(0,0,1/x^2)`, eta cancels
identically. Derivatives of q are retained, so this is a coupled rank-five
current module, not a one-direction scalar projection. It solves the
pure holomorphic first-current residual.

`log_search.py` uses the parent's three exact D2-logarithmic vector fields.
It also builds the six simultaneous D1*D2-logarithmic fields
`D1*X_i` and `(X_j D1)X_i-(X_i D1)X_j` and verifies both tangencies exactly
over QQ. Coefficient divergence, feature derivatives, all GM rows, and the
weight are retained. Additional gauges test simple D1/D2 poles and the
factored Jacobian (which cancels the artificial Delta47 weight).

`pullback_factors.py` exactly factors the physical pullbacks of the three
initial frame denominator factors. Important distinction: D1 and elliptic
D2 are the actual singular-curve loci; HolD, called `D` in that algebraic
packet, is an apparent selected-frame denominator. In particular the
2531-term physical Phi factor belongs to HolD, and is coprime to Delta47;
it is not the geometric discriminant. The initial informal opposite naming
was corrected before any geometric exclusion was made. All saved products
were checked exactly over QQ.

Independent audits:

- `independent_audit.py/json` (rank_candidates) freshly reduces the actual
  pole-two source in the weighted Jacobian ring at twelve physical samples
  over three primes; source, transpose, Jacobian, frames, and logarithmic
  weights all agree.
- `audit_absolute_lift.py` and `absolute_lift_audit.json` independently verify
  the PLUS primitive `(Q8_W-W*Q8_h)/C_t` in 108 direct affine derivative checks.
  A universal divergence identity supplies its characteristic-zero sign.
  This supports the separate marked-point Abel--Prym construction, with no
  source-serving or primitive claim.

Every finite search stores arguments, point lists, column labels and exact
modular ranks in same-name JSON/pickle files. All runs use p=1000003. The
baseline degree-five hol/degree-three eta modules have ranks1188/1189;
the degree-five Higgs module has840/841. The simultaneous-log module with
simple D1/D2 poles has2376/2377, both in the original and theta frames.
No sampled positive survived to require QQ reconstruction. The gauge union
`higgs_gauged_d3` has dependent columns (rank1025 out of1500), so its modular
augmented rank1026 is only a finite-prime negative and is not promoted to a
characteristic-zero no-go without exact dependency bounds.

Example reproductions:

```
python search.py --degree 5 --eta 3 --frames physical --output physical_d5_eta3
python higgs_search.py --degree 5 --output higgs_d5
python log_search.py --gauges '1;D1^-1;D2^-1' --output log_D1D2_poles_d3_eta1
python log_search.py --basis theta --gauges '1;D1^-1;D2^-1' --output theta_log_D1D2_poles_d3_eta1
python independent_audit.py
python audit_absolute_lift.py
```

All files are private scratch research outside the protected repository.

## Marked-point trace module (bounded constructive extension)

`marked_trace_search.py` constructs eleven rational base two-forms from the
natural marked point `T=z,W=w/rho`, where
`Gamma:w^6+c*w^3+1+v^6=0`, c=5/7. The actual marked hol forms are MULTIPLIED
by rho and the conjugate marked hol form by rho². Pairing with the dual
Gamma characters gives six actual and five conjugate trace forms.
Writing u=w³ reduces all traces to u²+c*u+1+v⁶=0; the exact identity
`Tr(R/(2u+c))=coefficient_u(R)` removes the apparent Gamma discriminant.
The remaining marked tangent norm is proportional to
`G=(1+v^6)(1+av)^2-c*av*(1+av)+a²v²`.

The physical vector corresponding to `g da wedge dv+h db wedge dv` is
`(h,-g,0)`. Second jets of the physical parameter map provide the first
derivatives of these vectors, so current divergence retains every Jacobian,
charge, and primitive derivative. Both raw-rho and rho*fT densities are
available. Tensoring the eleven fields with all three Prym components gives
66 constant columns; all fields are nonzero and the sampled ranks are66/67.
Adding z and the known first current gives132/133 in the initial finite test.
These are constructive ansatz screens, not a geometric serving statement.

The marked divisor itself is birational to Gamma times P², hence hasH20=0;
its direct Gysin cannot solve the target. Also the exact independent
`../cyclic_full/schiffer_audit.py/json/pickle` shows that the source is not a
single Schiffer-at-T=z channel. The trace module is tested as a larger
rational-current span, with no inference from its nonzero Abel--Prym map.
`marked_fields_holdouts.json` supplies three numerical field/derivative
holdouts. The independent replay
`/workspace/research/round9/abel_prym/independent_trace_audit.py/json/log`
passes every value and first derivative using one-variable dual numbers,
native symbolic derivatives, and rawQ8 data; it imports none of this
evaluator's Model/Jet/Quad code.

The later globally clean eta frame and its literal holomorphic primitives
were also tested. Their constant-plus-z trace module has132/133; the matched
degree-two module remains a finite negative. The horizontal third-kind
extension that goes beyond proper H1 is now indexed separately in
`/workspace/research/round10/horizontal5/README.md`.
