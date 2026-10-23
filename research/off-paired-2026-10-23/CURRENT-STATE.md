> FINAL STATUS — 2026-10-23: Goal stopped at the user's request. UNSOLVED. Read [HANDOFF-2026-10-23.md](HANDOFF-2026-10-23.md) for the frozen handoff. Historical active-goal language below is superseded.

# Active certificate goal: current constructive state

The immutable off-paired target remains **unsolved**. No certificate, Lean
proof, local kernel verification, solve PR, protected CI result or acceptance
has been obtained. Partial research is not completion of the active goal.

## Current constructive priority: full-base compact source, all directions verified

Checkpoint 2026-10-22, 23:43 UTC. Still UNSOLVED; the goal stays active.
Read `audit/theta/COMPACT-SOURCE-AUDIT.md` and
`coupled-fresh/ruling-source/full-base-connection/FULL-BASE-COMPACT-PDE.md`.
The generic compact connection now has ALL three parameter directions,
all literal fiber primitives, and exact flatness. Independent audits pass
82 generic V groups, 886 full-base/primitive/flatness groups, and 32 actual
Euler-source/current/density groups. All are polynomial/rational identity
checks; none is Lean kernel verification or a solution.

In the descended basis over Q(i,j,v), let e_b select the b row, let
GammaV represent 6v partial_v, and set

```
D=6v partial_v-2i partial_i-j partial_j,
GammaD=GammaV-2i Gamma_i-j Gamma_j,
a0=54i^3 w(1+w^3)/(j^2 N), N=9i^2w^2-16j^2(1+w^3).
```

The exact original compact source, in flat physical volume di dj dw, is

```
R_w=(a0/6)*(4e_b-GammaD e_b).
```

It is also obtained after a known full-base Euler first current from the
single-IBP source. This current essentially reverses that IBP at the
cohomology level; it is not an independent compact-class cancellation.
The exact eight-vector, all current components and all fiber corrections
are serialized and independently audited. There is no inverse-map critical
denominator in R_w. ALL EIGHT entries remain unserved.

Volume binding is essential: formulas with coefficient 1/(12j) use
`di d(j^2) dw`; those coefficients multiply by 2j in flat `di dj dw`.
For example the original single-IBP compact source is
`v_w*(D-5)hsrc/(6v^2)*e_b` with the latter volume.

Fresh is pursuing a source-directed j primitive of R_w, using the literal
identity partial_j[y^2 dx/(2x^4)]=nu_b on the descended curve. Its full
compact correction and density derivative must remain. Theta has saved
an exact 848-by-80 logarithmic w presentation and actual residual source;
its cokernel dimension is 768 when the w-map is injective, not the earlier
760. This is an interface for horizontal source construction, not a solved
class or an unrestricted exclusion. Fixed-j,w i integration is a separate
constructive attempt. Fixed-u,w, with u=j^2/i^2, fixes the old physical
r,z ratios and must not repeat the excluded 65-fibration scope.

The J=1 bielliptic support route is also source-directed: a<->t is an
involution of the canonical curve when d=e. Its quotient is elliptic,
but b dq/J is anti-invariant. A useful source/Gysin construction must
retain its normal odd variation and every complementary component; the
quotient alone does not serve the target.

Correction to scalar K simplification: original regular CRT potentials
have H=K/v fold order at most three. Properizing the CUBIC moment can
raise it to FIVE. The preferred verified quadratic infinity preimage avoids
further increase, but does not restore order three. Safe fully properized
normal form is a constant plus U(w)/Ccrit^5, deg U<120. Its quartic source
has poles of order at most four and needs a current denominator Ccrit^3.
All metadata and the earlier q3/q5 scope have been corrected. The exact
scalar identity is unaffected. Universal polynomial-f serving still
requires actual H to be put in Q(i,J)[f], f=1/v; no trace or polynomial-w
substitution has done that.

Both origins were fetched about 23:42 UTC, and upstream main was fetched
read-only to FETCH_HEAD=59d570e2823d7c605decc3055dae392ec5b8d5f2. The research
branch remains clean at 21fccb6...; no branches or local changes were
replaced. Live off-paired has no solution files. Its instance.rec changes
only camera distance3.45->3.29313; exact F,A,q and variable order are
unchanged. Live record SHA256 is
76c31054fbe7d37ac547431a468e23ecd129d3d12c60612bad5aa553a409602d.
`upstream-verification-latest.json` binds the comparison and target tuple.
AGENTS.md, CONTRIBUTING.md and formal/README.md are unchanged upstream.
The public discussion was read again: same one own comment and three
replies. Original publication.json/unpublished endpoint candidate remain
unavailable/unaudited. No external write, certificate, Lean proof, kernel
verification, solve PR, protected CI or acceptance exists.

## Latest actual source: compact Green current and quartic integration

Checkpoint 2026-10-22, 23:24 UTC. The exact source remains UNSOLVED.
The scalar K construction is complete, and the introduced finite Pa
residue now has an explicit source-bound current. The remaining compact
forcing still requires a primitive. Do not mistake connection matrices,
local pole regularization or polynomial-density conditions for a solve.

### Explicit finite residue current and compact-only forcing

`coupled-fresh/finite-pa-current/ACTUAL-PA-GREEN-PRIMITIVE.md` evaluates the
already audited Green currents at the constant Pa residue. Write
H=Hsrc, fN=e^-5F, gN=e^-5G, hN=e^-1Hpot, M=e^-7K, Z=-B0, and let

```
V=H_e partial_e+Green_PE(fN,1)+Green_PD(gN,1)+Green_P3(hN,1),
X=V-M Z.
```

All three primal operators kill constants. The actual scalar reduction
therefore gives divV=e^-7(Z-1)K and divX=-M/2. Consequently

```
M(B0-1/2)zeta=div(X zeta)-V dot nabla(zeta).
```

The finite Pa residue has explicit primitive +/-sqrt(-1)*i_X(mu).
The remaining forcing is compact in just three literal directions:

```
-V_c bq dq/Jcurve -V_d q^3 dq/Jcurve -V_e b dq/Jcurve.
```

This repackages the source through its actual chosen potentials. It does
not cancel a compact cohomology class automatically; without the potentials
it reduces to the original first integration by parts. Its useful features
are the complete finite current and a source interface free of K, Theta
and companion forcing. Fourteen primary groups and fifteen independent
source/weight/Green groups pass in `audit/theta/verify_compact_three_row_source.py`.

### Fully generic compact connection, with exact primitives

`coupled-fresh/theta-compact/affine-V-generic-results.json` now contains a
fully generic connection for 2c partial_c+d partial_d+e partial_e, with all
333 cleared polynomial identities checked over Q(c,d,e). This supersedes
point witnesses for this direction. Its exact polynomial primitive columns
are retained. The descended rational rank-eight matrix is in
`rank8-descended-connection-results.json`, over Q(i,j,v), i=c/e^2,j=d/e,
v=e^6. The common denominator has degree four in v. The compact basis is

```
[1,q,q^3,q^4-Cp(Cp-d^2)q^2/8,a,aq+dq^2/2,b,bq] dq/Jcurve
```

with deck weights [1,2,4,5,1,2,4,5]. There is zero leakage to the infinity
residue quotient. The actual three-row compact Green source is being
integrated; no rational solution of that system is yet known. Theta owns
w-direction integration; ruling-source extends i,j connections so a
w-only sufficient condition does not restrict the original goal.

### Direct quartic kernel reduction

`audit/quadric-kernel/QUADRIC-KERNEL-REDUCTION.md` gives an alternative
literal current for the same actual source. Set ell=e q,h=e^-3 and retain
h^2=f(w)=1/v(i,j^2,w). The fixed quadric is

```
a^2+b^2+i ell^2+j a ell+ell+1=0, h=ab/ell^3.
```

The positive scalar remainder has an explicit current leaving
`-K b^2/(6 ell^4) da wedge d ell wedge di wedge dj`. Eliminating b^2 gives

```
P=a^4+j ell a^3+(i ell^2+ell+1)a^2+f(w)ell^6=0,
S=K f_w ell^2(a^2+j ell a+V)/(6P_a), V=i ell^2+ell+1,
```

as coefficient of d ell wedge dw wedge di wedge dj. Thirteen independent
symbolic checks verify this transport. With H=K/v and ucurve=1/a,

```
S=-(ell^2/6) H partial_w(1/a)
 =partial_w[-ell^2 H/(6a)]+ell^2 H_w/(6a).
```

The quartic trace of 1/a is zero, so the algebraic w connection has a
three-dimensional trace-zero block. Its generic exact matrix and source
are saved in `coupled-fresh/quartic-kernel/QUARTIC-W-CONNECTION.md` and
`quartic-w-connection-results.json`. The source still has to be integrated.
A sufficient constructive condition is actual H polynomial in f=1/v;
then substitution f=-a^2(a^2+j ell a+V)/ell^6 gives a rational polynomial
antiderivative with no logarithms. Actual H has NOT been placed in that
space, and polynomial in w or a weighted trace is not a replacement.

### Exact source-lift freedom and pole simplification

For any rational Q, deltaF=v ZQ has alpha(deltaF)=dQ and preserves all
actual residues. The exact intertwiners are

```
PE(vZQ)=(Z-1)[v LE Q], LE=D(D+1)+A(Z+D/2+2),
PD(vZQ)=(Z-1)[v LD Q], LD=4JB^2+2B+A(Z+JB+1),
P3(vZQ)=(Z-1)[v L3 Q], L3=A^3+v(Z+JB+2)Z(Z+D/2+5).
```

Thus K/v changes by known differential operators on Q. Properizing the
initial exact moments removes the entire degree-24/i^-7 polynomial
primitive contribution. Full K/v has no finite fixed poles after the
served N residue; its only possible finite poles are introduced simple
critical folds. Fifteen exact valuation/tangency groups pass in
`adjoint-reconstruction/actual-k-fixed-divisors-results.json`.
A generic exact rational q3/q5 Hermite interpolation regularizes K at all
folds; `ACTUAL-FOLD-REGULARIZATION.md` specifies it without an enormous
expansion. Root independently verified the full lower fold map in
`audit/quadric-kernel/verify_fold_lower_map.py`. For the original unproperized CRT quartic source a lighter one-step rational
Hermite current suffices. Full cubic properization can raise H fold order
to five; then the source needs a higher Hermite current through order four.
In both cases 1/a is even in the Morse coordinate and the residue is zero.
The lower and regular source terms are retained.

Physical Pa transport also passes eight checks in
`audit/quadric-kernel/verify_physical_pa_residue.py`. A rational Pa sheet
chart and a full isotrivial genus-two connection retain all second-kind
components j=3,4. Arbitrary rational densities are not integrated by
rationality alone. The finite Pa current above already serves this
particular residue without imposing a w-only primitive.

No certificate, Lean proof, local kernel verification, solve PR, protected
CI or acceptance exists. Both repositories remain clean; last successful
fetch/public HTML refresh was about 22:10. Original publication.json and
unpublished endpoint candidate remain unavailable and unaudited. No
external write has occurred. The active goal continues.

## Latest actual-source construction: explicit rational K, retained curve defect

Checkpoint 2026-10-22, 23:05 UTC. The scalar rational reduction is now
constructive and verified. It does not yet serve the curve-valued kernel,
and the original sextic remains unsolved.

The authoritative source arrays are
`coupled-fresh/genus4-gm-independent/corrected-rational-source-binding.json`,
source SHA256 d725307869fcf3a2f064a0a6616eee78ea59f74dd3305fcb1d2408d3018f25b5.
The differentiated source is Ssrc=(Dc-6)(Dc-5)hsrc. Its actual finite-N
residue is i^-1 rTarget, where u=J/i^2 and

```
rTarget=2(theta+1)(2theta+3)r_h
       =4u^2 r_h''+14u r_h'+6r_h, theta=u partial_u.
```

Do not substitute the undifferentiated r_h or discard i^-1. The exact RIGHT
Ore identity L1 U+L2 V=1 serves this actual profile; root checked all six
arbitrary-function coefficients. Independent Fraction source binding and
residue-map verification passes 45 exact groups in
`audit/ruling/verify_actual_residue_map_fraction.py`.

The construction has advanced beyond a conditional fold/pole reduction.
With alpha(F)=F dv/v^2 along w, literal Cartan transport gives

```
alpha(Ac F)=partial_i alpha(F)-d_w(F v_i/v^2),
alpha(Bc F)=partial_J alpha(F)-d_w(F v_J/v^2),
alpha(Zc F)=alpha(F)+d_w(F/v).
```

These identities retain all fold and boundary poles as rational exact
corrections. The chosen CRT polynomial tLift is divisible by w*T*Lden;
therefore tLift*dlog(v), alpha(hsrc), alpha(F), alpha(G) have only N as a
finite pole. Their actual differentiated N residues cancel. All other
finite residues vanish by the literal transports, and infinity follows by
the residue theorem. Thus a rational K exists without assuming a selected
Hermite system is consistent.

An explicit K is now saved in
`coupled-fresh/ruling-source/adjoint-reconstruction/N-ONLY-RATIONAL-LIFT.md`
and `n-only-hermite-results.json`, also summarized in
`coupled-fresh/genus4-gm-independent/ACTUAL-RATIONAL-K.md`.
Over QQ(u)[w], complete Hermite reduction of the three i-weight components
passes every full derivative polynomial identity and has zero final simple
remainders. Their polynomial primitive degrees are 12,2,24. The full
literal formula K=v(H_N+Ctot) restores all Cartan terms and satisfies

```
Ssrc-LE(F)-LD(G)-L3(Hpot)=(Zc-1)K.
```

The independent audit inspected the exact global checks and passed 13
additional Fraction checks of the polynomial split and serialized
primitive derivatives. See `audit/ruling/SOURCE-RESIDUE-CURRENT-AUDIT.md`.
The earlier degree-24 fold CRT leading-current construction is now
secondary; it is not needed to justify this all-pole rational lift.

The main open obligation is the ORIGINAL CURVE kernel. With mu=dc dd de,
Zc=(c/3)partial_c+(d/6)partial_d+(e/6)partial_e=-B0,

```
e^-7(Zc-1)K zeta
 =div(e^-7 K zeta Zc)+e^-7 K(B0-1/2)zeta.
```

The last term is retained. The scalar K identity is not an original
primitive or a certificate. Keep the full freedom K -> K+v C(i,J).
The displayed scalar convention uses positive Ssrc; the original target
requires its overall negative after source integration by parts.

A source-specific moment now transfers the defect without losing any
compact component. On the normalized curve ab=q^3,
Q=a^2+b^2+cq^2+daq+eq+1, Jcurve=2a^2+daq-2b^2, set

```
Theta=b^3 dq/(3q^2), Cp=c-d^2/4,
kappa=d(Cp^3+8)/16, omega=q^2 dq/Jcurve,
Ftheta=b^3/(3q),
OmegaTheta=Theta+(e/2)zeta+d_q Ftheta+kappa omega.
```

OmegaTheta has no finite poles and zero infinity residues; higher
second-kind infinity poles remain. The PLUS kappa omega sign is verified.
The full weighted transfer for M=e^-7K is

```
M(B0-1/2)zeta mu
 =d JTheta+[-M_e OmegaTheta+(e/2)M_e zeta+kappa M_e omega]mu,
M_e=e^-8(Dc-7)K.
```

All three remaining components and the derivative of the density must be
kept. Fifteen exact symbolic groups verify both polynomial representatives,
finite principal parts, independent infinity series, sign, and compact
derivative in `coupled-fresh/infinity-horizontal/THETA-COMPACT-MOMENT.md`.
A new generic nine-class affine reduction (including the infinity class)
has constant nonzero determinant; full compact/source closure is active.

No mathematical certificate, Lean proof, local kernel verification, solve
PR, protected CI or acceptance exists. Both repositories remain clean;
latest successful origin fetch and public discussion HTML refresh were
about 22:10 UTC. The live read showed the same one own comment and three
replies. Original Mac publication.json and unpublished candidate remain
unavailable and unaudited. No external write has occurred. The goal stays
ACTIVE, UNSOLVED.

## Current priority: toric source, full genus-four closure, coupled sections

Checkpoint 2026-10-22, 22:24 UTC. The exact source now has a simple third-kind
potential on the canonical curve, beyond the older ruling construction:

```
zeta=b dq/q, eta_b=b dq/J,
partial_E zeta=eta_b, tau=-partial_E^2 zeta,
(partial_E^2-partial_T partial_C)zeta=0,
(partial_D^2-partial_A partial_C)zeta=0,
(partial_A partial_B partial_T-partial_C^3)zeta=0.
```

These universal identities are literal at fixed physical q. The first
point-pair form chi=zeta/b0, b0^2=-T/B, has residues +1,-1 at
`a=q=0,b=+/-b0`. It has zero infinity residues and retains fourth-order
second-kind infinity poles. Its universal derivatives and residue signs are
in `coupled-fresh/infinity-horizontal/TORIC-POINT-PAIR.md`. The companion
`xi=a dq/q` is different: when D is nonzero it has nonzero infinity residues,
so the proposed zero-residue analogy for xi was incorrect and has been
corrected. All subsequent companion formulas retain its omega_inf term.

`coupled-fresh/ruling-source/NORMALIZED-MODULI-DENSITY.md` gives exact moduli
(c,d,e), actual source density Hsrc and an algebraic integrating factor for
one outer adjoint. Seven exact symbolic groups passed. The full density
must stay in every current; this is not polynomial-density integration.

Three explicit source-current operators, their exact adjoints, rational
Cartan fiber primitives and base Green currents are in
`coupled-fresh/ruling-source/adjoint-reconstruction/CHI-THREE-OPERATOR-CURRENTS.md`.
The actual sufficient equation is

```
PE* f+PD* g+P3* h=-partial_e^2 Hsrc.
```

The search script uses the opposite right-hand convention, so any candidate
must be negated for that reconstruction. The exact primary operator
identities passed ten symbolic groups. The normalized operators are NOT
literal zero at fixed normalized q: their stated fiber-exact Cartan terms
are essential. Small source-directed multiplier trials have no candidate;
these are feedback only, not new unrestricted exclusions or completion.
The trial loop stopped rather than increasing arbitrary degree.

The complete genus-four compact reduction is now explicit:
`coupled-fresh/genus4-gm-independent/COMPLETE-RR-CONNECTION.md`. Riemann--Roch
constructs a complete marked-point basis of dimension eight and intrinsic
exact-primitive spaces. All six universal coefficient GM matrices passed
48 exact cleared identities at the physical point modulo 1009. Three first
and six second physical chi derivatives have rank seven; adding ten third
derivatives gives rank eight, with pivots R,S,z,RR,RS,Rz,SS,RRR and nonzero
pivot determinant 822. All 19 compact-plus-exact identities pass. Eleven
annihilators have generic rational determinant reconstructions with explicit
fiber primitives. The numerical rows witness nonzero generic pivots; they
are not themselves rational coefficient lifts or a solved source equation.
Full cyclic closure beyond these generators is not assumed without its
additional connection relations.

Independent audits are in `audit/ruling/TORIC-HEAT-AUDIT.md`: 14 literal
checks, 185 operator/physical third-jet checks, and 228 Newton-root checks
at twelve fresh finite-field curve points. The latter independently check
all 19 physical chi jets, their primitives, rank eight and pivot set.
The corrected compact companion psi_hat has also been reduced in the
complete RR8 basis with its infinity correction and an exact primitive;
see `cross-compact-source-reduction-results.json` and
`cross-source-chi-operator-results.json` in the GM directory. Its actual
rational forcing match is not yet solved.

A new coupled-section route is active. Universally,

```
partial_B partial_E xi+partial_C^2 zeta=0,
partial_B partial_T xi+partial_C partial_E zeta=0.
```

The normalized cross-current must retain xi's finite and infinity residues.
The infinity agent derives a paired adjoint condition that cancels both
with the same multiplier, rather than discarding one. Source-match agent
is pursuing this broader constructive system; no current is yet a solution.

A separate global Cayley first current is exact for the actual quotient
source on its host: `endpoint/global-serving/GLOBAL-CAYLEY-SOURCE.md`, with
21 exact checks. Its inverse Gysin meets a nonzero odd ruling-cover
residue. The rational discriminant and Fano host do not close that residue.
The source/cylinder normalization remains uncalibrated and it is not a
certificate.

The actual moduli branch Delta is distinct from the six older D18 graph
supports. Its base surface becomes a fixed CM genus-four curve times an
explicit base curve after a finite root cover, retaining the k character.
There are explicit holomorphic base two-forms, but their pullbacks to the
vertical divisor have zero proper H31 Gysin by naturality over the rational
base. A useful target-serving class would need a mixed fiber/base component
or an actual boundary transgression. No automatic source match is claimed.

Both worktrees remain clean; origin was fetched again about 22:10 UTC.
The public discussion HTML was successfully refreshed then and shows the
same one own comment and three replies. gh's earlier 401 remains recorded.
Original Mac publication.json and candidate are unavailable, and there has
been no external write. The original unpublished candidate has not been
audited. No certificate, Lean proof, local kernel verification, solve PR,
protected CI or acceptance has been obtained; the goal remains active.

## Latest source-carrying ruling identities (2026-10-22, 21:57 UTC)

The current priority is the actual canonical genus-four family in
`coupled-fresh/infinity-horizontal/RULING-NORMAL-FUNCTION.md` and the
all-parameter identity in `coupled-fresh/ruling-source/SHEAR-SOURCE-IDENTITY.md`.
This is a source-specific positive construction, not a new bounded search.
On `ab=q^3` write

```
Q=Aa^2+Bb^2+Cq^2+Daq+Eq+T,
(A,B,C,D,E,T)=(1+r^2,1+s^2,k/3,zk/2,z/2,1+z^6), rs=k^3.
J=a Q_a-b Q_b, eta_b=b dq/J, mu=dr dk dz/(9r).
```

The original source is exactly `tau mu`, where
`tau=-nabla_E eta_b=-nabla_T(q eta_b)`, with the orientation specified in
those files. The normalized ruling form beta has finite residues +1,-1
on the two degree-three ruling divisors. Its infinity residue is corrected
by `beta_hat=beta-c_inf omega_inf`. Beta_hat still has nonzero third-order
second-kind infinity poles; these have not been removed.

Put `Cp=C-D^2/(4A)` and use the algebraic coefficients rho,lambda,c0 of the
ruling note. The full shear `S=partial_D+(D/(2A))partial_C` fixes Cp,rho,
lambda,c_inf and gives the literal identity

```
nabla_S beta=d_q F_S-[lambda Cp/(A rho)] q eta_b,
F_S=lambda Cp (q+E/(2Cp)) b^2 q/[A rho J(b+rho)].
```

It holds at the actual nonzero mixed coefficient D, without specializing
D=0. For beta_hat retain `-c_inf nabla_S omega_inf` on the right. With
`h=A rho/(lambda Cp)` and `d=h c_inf=3AE/(2B Cp c0)`, the complete source is

```
tau=nabla_T(h nabla_S beta_hat)
    +d nabla_T nabla_S omega_inf-d_q[nabla_T(h F_S)].
```

Here d is T-constant but h is not. Forty independent standard-library
Fraction groups passed in `audit/ruling/verify_ruling_fraction.py` and
`audit/ruling/RULING-SOURCE-AUDIT.md`. These check the exact target source,
finite and infinity residues, literal variation and moving-pole exact term.

Actual physical lifts and weighted adjoints are saved in
`coupled-fresh/infinity-horizontal/actual_ruling_adjoints.py` and
`actual-ruling-adjoints.json`. Set R=r^2,S=s^2,k^6=RS, so the base density is
proportional to `R^(-5/6) S^(-5/6)dR dS dz`. The first source current leaves
`hT q eta_b`, with `hT=div_mu(VT)+2vT`. The shear current then leaves

```
g beta, g=div_mu(h hT VS).
```

At R=S=z=k=1, `g/h=-241/9`. The JSON uses the opposite residual convention,
so its stored value is +241/9. This is a nonzero remainder of this explicit
current, not an unrestricted obstruction. In terms of beta_hat it retains
both `g beta_hat` and `g c_inf omega_inf`. The ruling residue of the partial
current is a base two-form whose exterior derivative is g mu; that exactness
is automatic and cannot supply the missing closed residue current.

A second translation identity is now being independently checked:
`VE=partial_E+(E/(2Cp))partial_T` fixes rho and gives
`nabla_VE beta=d_q F_E+(lambda/rho)[D eta_b/(2A)+3q^2dq/J]`.
The q^2 term is `(VE c_inf)omega_inf`, so the corresponding beta_hat formula
retains only `lambda D eta_b/(2A rho)-c_inf nabla_VE omega_inf` plus exact.
Together with the shear and literal source identity, this offers a full
second-order relation for a source-preserving correction. No physical
adjoint solution of that relation is known. The ruling, infinity, coupled
and independent-verifier agents are working on it; no certificate exists.

## Latest primary rank-four constructive mechanism

### New background elliptic source decomposition

`coupled-fresh/infinity-horizontal/BACKGROUND-ELLIPTIC-SOURCE.md` is a new
source-specific geometric interface, with nine primary exact identities and
independent map/source checks. On the actual background curve with H,z fixed,
put `K0=1+z^6-H` and use q rather than C:

```
P=a^4+a^2(K0+zq/2)+q^6=0,
b0=q^3/a, s=a+b0, d=a-b0,
s^2=2q^3-zq/2-K0, d^2=-2q^3-zq/2-K0,
phi dC=(dq/12)(1/d-1/s).
```

Thus the actual source differential comes from the two elliptic Prym
factors of this genus-four curve. The third quadratic quotient is the same
universal genus-two family at parameters (K0,z/2). Crucially the original
endpoint still uses `C=q/3+z(s+d)/4`, coupling both elliptic factors. No
endpoint kernel, horizontal derivative or source factor may be dropped.
No relative Picard statement or primitive has been proved from this split.
This differs from the old fixed-C genus-nineteen curve and the old fixed
H-3zC/2 elliptic routes. The infinity and verifier agents are pursuing an
actual source-retaining correspondence/current, rather than an isogeny or
another bounded exclusion.

The exact rank-two elliptic connections, including all fiber primitives,
are now in `BACKGROUND-ELLIPTIC-CONNECTION.md` and the adjacent JSON/generator.
For `y^2=Aq^3+Bq+D`, use A=+/-2, B=-z/2, D=H-1-z^6. All four parameter
reductions, flatness and Euler identities passed eight symbolic groups.
The physical matrices are M_H=M_D and M_z=-M_B/2-6z^5 M_D. Fiber-exact
terms create endpoint C derivatives when integrated by parts; retain them.

On the relative product Eplus times Eminus, the two invariant translations
give genuine source normal velocities. If delta=qplus-qminus and
`Cext=(qplus+qminus)/6+z(s+d)/4`, then W=Dplus+Dminus is area-divergencefree,
W(delta)=s-d=2y^3 on the diagonal, and its contraction gives precisely the
actual elliptic source differential up to the stated normalization.
The companion Wprime=Dplus-Dminus has Wprime(delta)=s+d=2a. On the diagonal
`W(Cext)=a/3-z^2/8` and `Wprime(Cext)=y^3/3+3zq^2/2`.
Do not restrict these expressions before taking further derivatives.
The q^2 elliptic one-forms reduce to exact plus holomorphic terms, but
integration against the endpoint kernel generates further derivatives.
The endpoint agent owns this actual coupled normal-translation current.

The first source current in (H,q,z) has a retained correction
`[zq^3 M_C omega0/(144s^2d^2)+(s^-3-d^-3)omega0/144] dH dq dz`.
Its physical C_H factor rationalizes, while its elliptic H derivative is
genuinely second-kind. Both endpoint and elliptic connections are being used;
no cancellation of this correction has been obtained. An alternate literal
rank-four H-current is also saved by the coupled agent. The older R0 pole
interpolations only introduce/remove auxiliary poles and must not replace
this actual source problem.

### Complete bare physical equation and genuine source currents

The newest complete compact-module formulation is
`coupled-fresh/rank4-relative/BARE-FULL-HORIZONTAL-CLOSURE.md`.
Use actual bare coordinates `(a,C,z)`, with
`q=3C-3az/2`, `H=a^2+q^6/a^2+z^6+qz/2+1`,
`delta=partial_C`, and `N=3H-2C H_C`. If `Lhat` is the actual
fourth-order cyclic operator along delta, the full forced equation is

```
-Lhat* G + partial_a U + partial_z W
  +2C delta[(H_a U+H_z W)/N]
    = -C/(3a^2) delta(q^3/N).
```

All derivatives differentiate the displayed physical H. There is no inverse
P_a in this forcing. Explicit reconstruction includes all four compact
components, an elementary source-restoring C-current, and the actual Piola
map to x,y,z. The independent audit
`audit/rank4-relative/BARE-FULL-CLOSURE-AUDIT.md` passed 32 exact Fraction
groups, including every reconstruction row and physical source factor.

`SOURCE-HORIZONTAL-BEZOUT.md` gives genuine rational U0,W0, polynomial in C,
with `H_a U0+H_z W0=-q^3/(6a^2)` exactly. Its denominator depends only on
a,z and an explicit nonzero resultant, not P_a or a C-critical denominator.
The source term then cancels exactly, leaving the constructive equation

```
Lhat* G = partial_a U0 + partial_z W0
           +H_z partial_a S-H_a partial_z S,
U=U0+H_z S, W=W0-H_a S.
```

Both G and S remain unknown. Fixed U0,W0 with S=0 did not close in an internal
specialized trial; that is not an unrestricted obstruction. Setting both
independent horizontal currents U,W to zero is the already excluded
fixed-X1/X0,Y1/X0 relative surface and must not be pursued as a new route.

### Infinity source matching and its remaining residue condition

`coupled-fresh/rank4-relative/INFINITY-ORE-SOURCE-MATCH.md` constructs exact
general-H Ore operators `Uop L+Vop M=1`. Here M is the compact projection of
the constant-residue differential p^2 dp/Z. Taking adjoints matches any
compact scalar forcing with `f=-Uop* sigma`, `xi=Vop* sigma`, retaining all
four components. This is not a primitive: the infinity residue must also
cancel. An actual rational horizontal curl
`xi=D_z P-T Q` would suffice; a genuine closed ambient two-form is more general.
Vop* commutes with T; the source phi_H/6 and the elementary-shifted source
differ by an explicit T-current. The normal density has an explicit genuine
a,z primitive, but integrating that density does not integrate the endpoint
kernel. The active agent `infinity_horizontal_current` owns this curl step.

The Ore source match and its T-commutation also passed 13 exact checks in a
separate operator implementation; ten independent Fraction groups supplement
the generic source-Bezout identity. See
`audit/rank4-relative/INFINITY-ORE-AND-BEZOUT-AUDIT.md`.

The newest simpler density/current transport is
`coupled-fresh/infinity-horizontal/RATIONAL-DENSITY-CURL.md`. With v=az,
`eta=-q^3 d(v)/(2a^2)` is entirely rational. It gives an explicit partial
curl of B(phi_H/6), leaving precisely `B theta(K)/(9H^2)` with
`K=q^2/a^2 (q/2-3C)D_z(v)+(2C/3)(q^3/a^2)D_C(a)`.
Six exact symbolic groups passed. The remaining term is not discarded.
This avoids logarithms in the primitive choice; killing a logarithmic
coefficient in a different normal primitive is not intrinsic class vanishing.

Source-guided Ore syzygies give the general-H operator B12 in
`coupled-fresh/infinity-horizontal/TWO-NORMAL-GAUGE.md`, matching the compact
source while killing C and C^2 exactly. Its rational physical source still
has a nonzero remainder. Potential nontrivial closed two-form classes must
extend from the physical base, rather than being assumed available
independently on a single fiber.

### Joint operator source homotopies

`coupled-fresh/rank4-relative/two-operator/COMMON-FACTOR-CLOSURE.md` recovers
the universal endpoint Euler and Picard-Fuchs operators from the actual
bare Lhat and Y=H_z partial_a-H_a partial_z using rational determinant
formulas. An exact nonzero 11 by 11 minor at a valid finite-field physical
point proves the determinant is a nonzero rational function. This is a
positive operator identity construction, not a source primitive.

The simple Euler density field E=a partial_a-z partial_z gives an explicit
free Hamiltonian shift of the source Bezout current. Its apparent EH poles
are Y-exact principal parts; removing those poles leaves the genuine D0
source class. This does not constitute an additional solve mechanism on its
own. Both G and S remain unknown in the main equation above.

### Physical adjoint transport

`ADJOINT-TRANSPORT.md` removes spurious P_a forcing through an exact density-
corrected conjugation and an explicit horizontal current. Its 22 independent
exact Fraction audit groups are in
`audit/rank4-relative/ADJOINT-TRANSPORT-AUDIT.md`. A bare C-only solve after
this transport is still the old relative surface, rather than genuine new
horizontal motion.

### Earlier normalized scalar form

The full compact endpoint current has a new scalar-adjoint reformulation in
`coupled-fresh/rank4-relative/SCALAR-HORIZONTAL-CLOSURE.md`. It retains all
four components, including both second-kind components, and all physical
H,C,z directions. With cyclic basis `s_j=nabla_C^j omega0`, j=0..3, its
fourth-order Picard-Fuchs operator L gives the single forced equation

```
-L* f + T U + D_z W = sigma,
T=D_H+(2C/(3H))D_C.
```

Here `sigma=phi_H/6` for the physical Jacobian correction, or
`sigma=-C D_C(phi)/(9H)` after an explicit elementary original-source
C-current. All derivations include `a_H,a_C,a_z` from the actual relation
`P(a,H,C,z)=0`, `phi=q^3/P_a`; holding a constant is invalid. Explicit
reconstruction produces all four H,C,z current columns from f,U,W.
The equivalence is for the entire compact endpoint module, not a claim
that arbitrary moving third-kind physical currents are classified by it.
The cyclic and horizontal identities passed 50 independent exact Fraction
audit groups in `audit/rank4-relative/SCALAR-CLOSURE-AUDIT.md`; both primary
verifiers also reran successfully. Signs, all source shifts and every
physical derivative match the immutable target.

The adjoint admits a denominator-free Euler expression after
`f=C^2(4C^6-729H^4)g`. This gives a source-specific operator construction
to pursue with the exact normal antiderivative and the low physical
y-degree of A. No rational f,U,W has yet been found. The active agent
`coupled_current_fresh` owns this calculation; consult its newest files.
The particular shift `g=Rnormal/C^3` places all three explicit normal
antiderivative terms in roots of one Euler factor, but physical C derivatives
of a remain nonzero. A fixed-a calculation alone is not a source identity.

## Complete source interfaces

Read [the cubic-ray interface](cubic-ray/INTERFACE.md) and
[the complete closed-two-form criterion](audit/cubic-ray/CLOSED-TWO-FORMS.md).
On the full G36 quotient the actual residue is

\[
 R\Omega=\frac{Bp}{(B+3Cp^2)^3}\,
 \frac{dz\wedge dU\wedge dK\wedge dt}{18tz^2},\qquad
 H+Bp+Cp^3=0.
\]

Every rational primitive, after the stated finite-group averaging and trace
projection, is represented by the complete two-component finite connection.
The constants must be taken over the complex numbers for the unrestricted
contract. Rational matrix data do not restrict arbitrary solutions to Q.

The newest simpler rational cover uses `Z=1/z, h^6=t, u=U, v=K/h`.
Its actual volume and coefficients are

\[
 \Omega=-\tfrac13 dZ\wedge dh\wedge du\wedge dv,
 \quad H=1+Z^{-2}+h^6,\quad C=Z^2+u^6+v^6,
 \quad B=u/2+hv/3+huv/(2Z).
\]

It retains the full source `R Omega`, with the same root p. The degree-six
deck transformation `(h,v)->(zeta6 h,zeta6^-1 v)` fixes H,B,C,p and the
volume. A completed current can therefore be averaged/traced back to the
G36 interface and lifted to the original target. Eleven direct checks and
44 independent Fraction checks of the complete chart/K3 correspondence
passed; see `audit/cubic-ray/CONSTANT-K3-AUDIT.md`. The fixed-C Fermat
double-plane K3 and its two fixed elliptic factors retain all of H,B,C and
the entire cubic kernel. Factoring the density does not integrate that kernel.

The complete finite correspondence is in
`endpoint/cubic-ray/horizontal-cm/K3-ELLIPTIC-CORRESPONDENCE.md`.
After `Z=c^3 Y,u=cU,v=cV`, one has `Y^2+U^6+V^6=1` and
`Omega=-c^4 dc dh eta1 eta2`. A further exact normalization
`a=ch,q=c^4p` gives

```
q^3+Btilde*q+S=0,
S=c^6+a^6+Y^-2,
Btilde=(VT/2)c^3+(V/3)a*c^2+(TV^2/(2Y))a,
source=-c^3 R dc da eta1 eta2.
```

Here R, kappa, V, W are unchanged, both elliptic factors remain, and the
canonical source becomes `(0,1/S)` with actual weighted divergence.
The twelve radial checks passed. Polynomial radial density alone does not
provide the missing primitive.

For the canonical flat bracket on pairs `(Z,h)` and `(u,v)`,
`{H,C}=-12 Z h^5`. This monomial bracket and B's linear h dependence are
the current positive algebraic lead for a full two-component correction.

The one-variable gauge is `V=F-1/3, W=HC R`,
`F=-H/(p(B+3Cp^2)), kappa=B^3/(CH^2)`. The two coupled current equations in
[the canonical operators](endpoint/cubic-ray/poisson/CANONICAL-OPERATORS.md)
remain open. Neither component may now be discarded by invoking a pure-current
or closed-time shortcut.

The geometric Galois cover of the kappa equation is rational, rather than
the elliptic cover of the normalized parameter j:

\[
 \kappa=-\frac{27q^3}{(1+q^3)^2},\qquad q=S/T.
\]

Its deck actions over C are `q -> zeta3*q` and `q -> 1/q`. The exact bridge
to the elliptic presentation and source functions passed 26 independent
Fraction checks in `audit/cubic-ray/verify_rational_kappa_fraction.py`.

The [B-coordinate coupled partial current](coupled-fresh/COUPLED-B-CURRENT.md)
has exact remaining correction `-3 H_B/(4B^2)*(1,6)` to be constructed.
Its nontrivial first current uses both canonical components and satisfies
all 14 source/coordinate checks. Holding z,U fixed would return to one of
the already excluded original-ratio surface fibrations. A correction must
use the horizontal directions as well.
Its correction also equals `+5 H_B F0`, where
`F0=(3Cp^2-B)/(10g^3)` and `p_BH=-10F0`. The latter is an exact scalar
simplification of the outstanding target, not a cancelled remainder.

## Actual first primitive and remaining source

With `g=B+3Cp^2`, `Q={H,B}_0+3p^2{H,C}_0+2p^3{B,C}_0`, the absolute closed
two-form

\[
 \beta=d\!\left[-\frac{p^2(dB+3p^2dC)}{2Qg}\right]
\]

satisfies

\[
 \beta\wedge\omega=
 \left(R-\frac{p^2\{g,Q\}_0}{2Q^2g}\right)\Omega.
\]

Here `_0` holds p fixed. All derivatives of Q are included. The remainder
is nonzero and retains its Q poles. It is regular at a generic cubic branch
only on the explicitly stated coordinate opens; this is not a logarithmic
extension at every boundary. See
[the actual current](jacobian/CLOSED-TWO-FORM-CURRENT.md) and its independent
36-check Fraction audit. An unrestricted closed rational two-form of trace
R would give a primitive; no such form is known here.

## Fixed elliptic cover and a new coupled Fano organization

The complete normalized cubic has the fixed elliptic Galois curve

\[
 E:Y^2=X^3-16,\quad
 \rho^3=H/C,\quad p=-4\rho/X,
 \quad B/(C\rho^2)=(X^3-64)/(4X^2).
\]

Its degree-three isogeny to `E':V^2=U^3+432`, complete kernel, all three
root translates, actual source trace and finite-group inverse operators passed
40 independent Fraction checks. See
[the cover audit](audit/cubic-ray/ELLIPTIC-COVER-AUDIT.md). These difference
operators do not construct a differential primitive. The existing paired
scalar primitive retains a nonzero physical density derivative in the same
standard S3 character; applying the inverse operator does not erase it.

The Fermat presentation retains the entire coupling:

\[
 G_1=S^3+T^3-H=0,\quad G_2=c^3-C=0,\quad
 Q_B=B+3cST=0,\qquad p=-(S+T)/c.
\]

Writing `L=S^2+ST+T^2`, the normal determinant is
`-27c^3(S^3-T^3)`. The original four-form is its three-normal residue with
the exact numerator

\[
 N=-\frac{3ST(S^2-T^2)}{L^2}.
\]

The actual first-stage elliptic identity is

\[
 \delta_E=3T^2\partial_S-3S^2\partial_T,\quad
 q_E=-\frac{S+T}{2L},\quad \delta_Eq_E=N,
 \quad q_E\delta_EQ_B=\frac{9c}{2}(S^2-T^2).
\]

Thus integrating by parts leaves a polynomial double-normal coupling source;
it does not allow Q_B to be held fixed. Eliminating c gives the exact moving
ternary sextic

\[
 G_{\mathrm{eff}}=C+\frac{B^3}{27S^3T^3}.
\]

The second auxiliary variety, with weighted coordinates `(Y0,Y1,Y2,c,d,e)`
of weights `(1,1,1,2,2,2)`, is the Fano threefold complete intersection

\[
 Q_B=0,\qquad C-c^3-d^3-e^3=0
\]

of degrees two and six. It contains every B term. Its physical boundary
transport retains both d and e residues; deleting their poles is invalid.
The current constructive obligation is an actual parameter-compatible
two-normal primitive or a joint family retaining all mixed derivatives.
Separate Fano primitive theorems do not supply that compatibility. Consult
live agents and their newest files before duplicating this active work.
The full ordered source transport and boundary signs passed 27 independent
Fraction checks; see [the Fano audit](audit/cubic-ray/FANO-NORMAL-AUDIT.md).

The next finite boundary-jet reduction is in
`scaling/boundary-jets/actual-source-finite-jets.md`. Fermat division gives
explicit invertible degree-nine and degree-fifteen operators whose
determinants equal one at lambda=0. They reduce the four actual first-jet
targets, with rational divergence corrections, into ten pole-one and ten
pole-two plane-sextic classes. The checker verifies all 191 operator columns
and the physical derivative formulas. This supplies finite source jets,
not primitives for those twenty classes.

A subsequent relative normal-chain identity, independently audited with
twenty exact check groups in `audit/cubic-ray/BOUNDARY-CHAIN-AUDIT.md`,
uses the full closed rational one-form
`dlog[t_aux/(G_eff-t_aux)]`. It expresses the auxiliary source as a rational
exact term plus its actual twenty-class logarithmic residue module, and
makes the external parameter derivatives explicit. It does not remove the
logarithmic coefficient or serve the remaining module classes.
Replacing relative differentiation by absolute differentiation adds
nonzero external `H_D` terms and `-d_ext rho wedge dlog`; the updated
construction keeps these terms. They vanish under a particular external
top-three-form wedge, but cannot be dropped after contractions.

## New actual coupled currents and graph geometry

`jacobian/quotient/COUPLED-EULER-CURRENT.md` gives an explicit first current
using both components for its completion. In the constant-density chart set

```
E=h partial_h-v partial_v,
K=2C h^6-H v^6,
L=2(Z^2+u^6)h^6+(1+Z^-2)v^6,
U=E/(12K),
P=[(27-2kappa)/(2(4kappa+27))]V+W,
c0=3(27-23kappa)/(4kappa+27)^2.
```

Exactly, `div(VU)=R-LV/(2K^2)` and `dP=c0 V dlog(kappa)`.
A divergence-free rational D with
`D(log(kappa))=L/(2c0 K^2)` would complete the actual current
`VU+PD`. No such D has been found. Nine exact checks passed. This keeps
nonzero `div A` and independent current components, unlike the excluded
pure-V shortcut. Restricting D to the E direction returns to the old
genus-two endpoint; genuine horizontal Z/u motion remains necessary.

Fixing the new nonlinear ratios u,v also gives a source-retaining genus-four
curve model with holomorphic basis `(1,h,h^2,p)dh/g`. A complete first
relative current removes the generic g branch and leaves

```
R Omega = d[-p^2 dZ du dv/(6 g qh)]
          -5p^2 h^4 dZ dp du dv/qh^3,
qh=f_h.
```

See `quotient_geometry/fixed-uv/source-retaining-curve-model.md` and its
four-check exact current. This is an unintegrated qh-pole source, not a
new serving theorem.

The K3 first-angle graph has an exact selected-sheet rank-two evaluation:
if `Qang=(u^6+v^6)^2/(u^6 v^6)`, then
`kappa=(Qang-16)^3/(16 Qang^2)`,
`V=2(Qang-16)/(3(Qang+32))`,
`W=-16 Qang(Qang-16)/(Qang+32)^3`. The seven graph checks retain both
components. A bare elliptic diagonal kernel has the wrong S3 parity for
the actual source; its odd coefficient and normal jets remain to construct.

Weighted resolution of a Y-angle D18 graph exposes an exceptional surface
`m_jk(X) w^2=b^7+b` over `HX=0`. For graph pair (Y0,Y1), a concrete
target-invariant H20 candidate is proportional to
`dx wedge db/(z^3 Aaux^3)` in its weighted exceptional coordinates.
It comes from explicit j1728 elliptic quotients of two Delsarte curves.
The entire invariant exceptional H20 space is four-dimensional, with all
four forms recorded explicitly. Its geometry, full G36 character and actual
target normal jet passed 26 independent exact Fraction audit groups in
`audit/cubic-ray/EXCEPTIONAL-SOURCE-AUDIT.md`. The fixed projective orientation
gives the leading source `-t^25 Aaux^3/(6z^8)`.
This is genuine local geometry with the desired character, but its global
closed extension and source Gysin coefficient are unproved. A tentative
rational lift has a nonzero product-character term in its first derivative;
without a legitimate compactified holomorphic lift this is not an intrinsic
Kodaira-Spencer or nonextension theorem. Consult
`scaling/k3-cm-graphs/exceptional-source-character.md` before relying on it.
Local exceptional H20 alone is not a certificate.

## Fresh public result and routes to stop

The [18:10 UTC reply by `benediamond`](https://github.com/hodge-computer/sextics/discussions/57#discussioncomment-19129901)
proves an all-denominator obstruction to the old three-base contact equations.
The attachment was downloaded to
`/workspace/off-paired-contact-public-2026-10-22`; its zip SHA-256 is
`06ee0fdf55a3a5a2d82d5d0293df850220eb7afa1fe5fbe96f9b80a656fc31de`.
All 27 manifest hashes, exact target binding, both pole reductions and all
880 Jacobian multiples passed independent standard-library checks. See
[the public-packet audit](audit/PUBLIC-CONTACT-AUDIT.md).

A later [19:05 UTC reply by `deanodotdotdot`](https://github.com/hodge-computer/sextics/discussions/57#discussioncomment-19130946)
extends that old compact genus-two obstruction: every displayed j=0,1,3,4
current must move the modulus. The public gist was saved under
`/workspace/off-paired-public-three-component`; its portable checker passed
against the actual live instance, including every new adjoint identity and
the prior 880 scalar dual relations. It is basis-specific and does not
exclude the full four-component module or arbitrary physical primitives.
See `audit/public-three-components-verification.log`. No new solve is claimed.

The [20:21 UTC follow-up](https://github.com/hodge-computer/sextics/discussions/57#discussioncomment-19131907)
has a later gist snapshot, updated 20:50 UTC, saved under
`/workspace/off-paired-public-quotient-obstructions`. Its current README
states all single-character degree-seven exclusions, 30 of 36 degree-eight
characters excluded, and necessity of all five particular quotient-coordinate
components via relative-threefold second variations. All 21 downloaded
manifest files and exact immutable target binding were independently checked.
The contributor's unchanged standard-library threefold checker reran and
matched all five rank sandwiches. This is contributor-checker execution and
scope review, not an independent reimplementation or a Lean proof of the
toric/Hodge argument. See `audit/PUBLIC-QUOTIENT-READ-AUDIT.md`.
The theorem is coordinate-specific and does not exclude the full compact,
infinity or bare current constructions. It does not require both scalar U
and W to be nonzero; the eventual literal lift must retain the necessary
quotient components. No new public post was written.

The old contact theorem does not exclude the new complete four-base cubic-ray
module. A separate integrating-factor/Fermat-residue audit now excludes the
explicit pure-V, pure-W and relative-closed-time restrictions of the new
module, including their stated finite base extensions. See
[the exact scope](audit/cubic-ray/PURE-COMPONENT-AUDIT.md). The full coupled
system and arbitrary closed two-forms remain unrestricted.
The same proper Fermat moment gives necessary conditions for any solution:
`div A`, `A(log kappa)` and `D(log kappa)` must each be nonzero as rational
functions. It places no requirement that `div D` be nonzero. The independent
audit now includes 33 checks after adding these necessary conditions.

The factorization
`D3 D4=6X1 F_mixed+2X0^5 Y0^2` was also examined. The full fixed denominator
`D3 D4` does not solve the certificate identity (exact ranks 288/289).
This is a single fixed-denominator calculation, not a global exclusion.
The associated global H20 geometry notes require independent review; do not
substitute them for a solution or expand denominator powers without a
source-carrying construction.

One actual whole-cubic split graph yields the separate degree-18 denominator
`D18=F_Y*(X1^6+X2^6)^2+16*H_X*X1^6*X2^6`. The agent
`graph_denominator_construct` has built the complete fixed-denominator
modular system after polynomial gauge reduction: 20,085 rows, 5,291 numerator
columns, 549,582 nonzeros. At both primes 1000003 and 1009, the reported
coefficient/augmented ranks are 5220/5221; no candidate appeared. This is
scoped modular feedback, not a characteristic-zero exclusion. The independent
[D18 audit](audit/GRAPH-D18-AUDIT.md) verified exact target binding, complex
coprimality, both polynomial gauges, complete character enumeration, the
binary encoding, 20 exact columns and the full right side. It did not rerun
the large solvers. No denominator-power escalation was performed.

The three X-angle graphs and three new same-kappa Y-angle graphs were
also assembled with arbitrary degree-six sources in the complete
24-dimensional target character, imposing their sum equal A. The exact
certificate-addition interface passed an independent audit. No candidate
appeared modulo 1000003: the X-only system has ranks 15724/15725; the
six-support system has ranks 31466/31467 (149940 rows,31890 columns).
The six individual projected source spaces at that prime are the same
two universal Jacobian sources `X0 F_Y1/6` and `3Y1 F_X0/2`; all twelve
saved lifts passed full matrix substitution. These are simple individual
graph poles, not every possible mixed/product-denominator current or
exceptional higher-pole transport. See `graph-assembly/README.md` and
`audit/GRAPH-ASSEMBLY-AUDIT.md`. No powers were tested.

## Preservation and publication

Both repository worktrees remain clean. The isolated research worktree stays
at upstream `21fccb6b4f1d4070ddaa30195a78f268247569e6`; the original branch and
local files remain preserved. A later fork-origin/main cloud-setup merge is
not a newer mathematical upstream base and was not merged into this worktree.

The original Mac `publication.json` and unpublished candidate script are still
unavailable. They have not been audited. No live comment, gist or PR has been
changed. The original manifest must be reviewed before the requested in-place
publication update. The new public reply was read and audited, not overwritten.

Prepared with OpenAI Codex assistance and independent algebra, geometry and
verification agents. The mathematical primitive, local Lean verification,
protected CI and acceptance remain separate unachieved stages.
