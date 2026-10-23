> **STOPPED — handoff requested on 2026-10-23.** The user ended the research goal and explicitly authorized posting a GitHub handoff. All six research agents stopped; no certificate was obtained. The working notes below are historical and include superseded statuses. Read `HANDOFF.md` and the linked final agent handoffs before continuing. Do not resume searches without a new instruction.

# Active research portfolio

User objective: solve one open Hodge Computer target; keep working and use
multiple agents. User most recently said "Go". No verified solution has been
found. Exact target records and verifier must remain unchanged. No external
posting is authorized by the current conversation.

The main target remains **off-paired**. It was a heuristic easiest candidate,
not a mathematically certified difficulty ranking. The pinned sextics checkout
is `cb551854693127a2542fb405f7ceb47ae0b35a09`. A read-only upstream check found
no new solve PR; the newer upstream commits concerned rendering/navigation.

Before proposing small supports on a newly revisited target, consult
`alternate-audit/low_degree_e1_screen.json`: the initial all-target q1
first-E1 screens already excluded every denominator of degree1 through4
for the listed challenge instances, including eight-plane-configuration.
The modular rank sandwiches there are characteristic-zero exclusions,
not just failed sample searches. Off-paired has stronger later exclusions.
Repeated powers do not rescue a prescribed reduced support at q1.

## Main constructive work

- `round7/README.md`: exact source-bound elliptic Gauss--Manin reduction,
  bounded current searches and qualifications.
- `round7/moving_j1728/`: actual horizontal genus-two curve families with
  fixed elliptic j0 and j1728 factors; exact differential/Gysin formulas.
- `round7/moving_j0_audit/`: intrinsic degree27 slope cover, degree54 with
  the square-root twist. `bkk_degree.py` proves the isolated torus solution
  upper bound27 exactly. Smooth degree27 fibers and Frobenius patterns give
  the selected finite component and S27 monodromy (with the finite-etale
  specialization hypotheses recorded). This is not the standard E6 line cover.
- `round7/norm27/`: the universal norm is now proved by boundary valuations,
  and independently certified on a finite-field slice by interpolation with
  a sparse-resultant degree bound. It is `C(ell)*Q18^4/b2^3`, of geometric
  squareclass b2. Its quadratic character surface has irregularity zero;
  this does not exclude H1 of the actual degree54 surface.
- `round7/off_paired_pde/moving_line/`: Chebyshev elliptic quotients and
  exact source-bound boundary characters, including the genus11 boundary
  curve. Boundary forms have not been extended globally.
- `round7/moving_j0_audit/jacobian_factors/`: the boundary genus11 Jacobian
  splits into pairwise nonisogenous absolutely simple factors of dimensions
  1,2,4,4, certified at a good reduction. **Do not use the earlier rank5/K6
  test as an obstruction:** the corrected P-root chart is `v=U^10*n`, and
  those five proposed dual sections have poles. The conductor chart is
  smooth after exact second-jet cancellation. The bounded ambient closed
  1-form searches have only the expected exact kernels, also after removing
  the genus11 boundary constraints. Cycle and reflection now compute the
  actual normalization/linkage and compactification defect maps.

## Alternative targets being explored in parallel

- `round8/reflection_coupled/`: actual incidence-field source for
  reflection-coupled-residual, all 64 public replay checks passed; fresh
  bounded full two-component current searches and a multiplier first-integral
  search. No positive candidate.
- `round8/cyclic_companion/`: cyclic-triple-residual elliptic Fano companion
  and exact Jacobian-character counts. The whole companion's even sector
  contains H41, so no unsupported coniveau-two inference is permitted.
  Special fixed line divisors lie over a source-empty hyperplane.
- `round8/cyclic_pairs/`: exact QQ monic degree84 field model, compact charge,
  source tower and independent fiber checks. A rational gauge reduces the
  charge to `delta(log B)/6`. The actual curve is now proved geometrically
  irreducible using native finite-field factorization, a smooth rational
  point and exact coefficient reduction. It has no hidden smaller constant
  component. Native polynomial-matrix HNF/Popov is being used for the
  remaining integral-order computation; bounded natural-current searches
  have found no primitive. The degree84 enlarged-order weak-Popov basis
  is now exactly verified over F1000003[b] by a full inverse operation
  replay and an independent input audit (`round8/native_hnf/`). The
  corresponding colon ideal supplies a smaller trace-dual search space;
  its raw basis is now fully certified, including every polynomial kernel
  product. Norm(Q) has degree25200; the order index and colon determinant
  degree are9662. A reduced colon basis was not returned by capped runs.
  This scalar engineering is now parked. A second integral generator is
  available: `Z=tB*D*N^3*s/A^3`, `Z^2=tB^2*B/3`, with deg(tB)=9.
  Exact QQ local residue cancellation on the generic Delta0 divisor has
  passed; rational solutions must be regular there. None of these steps
  supplies a scalar primitive or a physical certificate.
- **The generic one-direction cyclic scalar route is now excluded exactly.**
  `round8/off_paired_B_resonance/resonance_obstruction.md` proves a
  two-place valuation obstruction over C(eta,V,s). Root independently
  replayed the limiting operator and source directly from the cleared
  Bred/Cred/rhsred polynomial equation, without compact charge formulas.
  The necessary univariate equation forces a polynomial of degree at most10
  to be divisible by a polynomial of degree12. This is not an exclusion
  of unrestricted certificates, and is not an exclusion on every special
  invariant level. Further fixed-level scalar expansion is parked because
  it cannot lift to a generic rational solution of this route. The cyclic
  agents now pursue the full coupled transverse connection and actual
  source corrections, including dG wedge C.
- `round9/cyclic_full/`: all three base connection matrices and relative
  exact corrections are derived for the rank3 actual-source eigensystem
  and its conjugate. Exact QQ flatness and an independent finite-prime
  jet audit pass. Root independently checked the actual sextic/numerator
  pullback, the oriented coordinate Jacobian and the universal canonical
  transformation. `round8/coupled_source/` retains the cube-root character,
  exact Jacobian factorization and the nonzero multiplier-derivative
  remainder after first integration by parts. The full three-direction
  twisted-divergence equation is being searched on the rational physical
  base; no positive yet. Delta47 is base-map ramification. A distinct
  irreducible2531-term Phi comes from the selected frame determinant;
  it is an apparent pole, as is thetaK. The clean global eta frame and
  complete Q8/Q14 primitives remove these factors exactly. The actual
  singular-curve factors are the branch-cubic discriminant D1 and the
  elliptic-quotient discriminant D2. The full module Der(log(x*D1*D2))
  is free: three explicit fields have determinant -120050*x*D1*D2,
  satisfy exact tangency, and contract the clean connection to polynomial
  matrices. See `round9/cyclic_full/CLEAN-FRAME.md`.
- `round7/alternate_construct/`: quadratic-cubic-pullback residual-sheet
  correspondence, exact trace-zero source and genus4 curve family over a
  bicubic CY3. No serving construction yet.
- Symmetric-sextic-residual: A3 quotient and pair-product quotient with exact
  density; a Laurent cubic is not automatically a Fano cubic. The generic
  genus3 Jacobian is absolutely simple, so the obvious elliptic-factor
  shortcut is closed. This branch is parked.
- `eight-plane-configuration`: a new exact two-plane projection gives a
  quartic fiber and tracezero rank3 residue algebra. Universal P1 Hermite
  reduction and source-preserving Ferrari flag transfer are verified; the
  actual residue packet is being bound to the target. `diagonal-permutation`
  pair-ratio quadrics were checked to have only six ordinary nodes each,
  so their Vandermonde union has no H20 serving direction. Other source
  geometries are being scouted.

The main geometric compactification has also advanced: the twisted Cox
model in `round7/boundary_extension/twisted_projective_model/` is a genuine
complete intersection with H1(O_X)=0. Its main-component normalization and
resolution can still contribute H1. The known local nonrational pieces
include a j0 exceptional curve at q=0 and j54000 elliptic curves
along the24 G conductors. Each of six J exceptional curves has genus7
and odd Jacobian isogenous to E0^4. The h=plus/minus2 residual surfaces
also involve explicit genus4 curves whose Pryms are being audited. These
pieces must be entered in the chosen compactification's exact sequences
without counting the same curve both as conductor and resolution data.
The connecting maps, not just the existence of these curves, are being
calculated. P-root exceptional curves are rational. The older
untwisted global model was not a complete intersection; do not use its
linkage shift globally.

Finite-field negatives, bounded search failures, existence of a holomorphic
form on an auxiliary variety, and fiberwise algebraic Kuga--Satake are all
distinct from a physical certificate. Positives must be reconstructed and
verified exactly and then bound to the protected Lean target.

## Current round9 constructive leads

- `round9/cyclic_full/global_eta_frame.pickle`: exact global actual-source
  rank3 frame now removes every apparent factor; only geometric D1,D2
  (and x for the x direction) occur, with simple poles. All holomorphic
  Q8 primitives are included and independently replayed.
- `round9/abel_prym/`: the marked t_old=0 section has a verified
  nonconstant Abel--Prym map, with a correct absolute lift. Its direct
  exceptional spread has zero H20, and unweighted trace vanishes.
  Eleven weighted traces against the fixed Gamma curve give nonzero
  rational current fields; all values and first derivatives are audited.
  A higher-pole extension gives24 fields. Finite low-degree current
  searches remain negative. The new pole is the corrected
  `G=(1+v^6)(1+av)^2-c*av*(1+av)+a^2*v^2`, not the earlier c=1 formula.
  Its base curve is genus2 with Jacobian isogenous to E0^2; the Prym
  family along its b-lines has no constant E0 summand (independent jet
  audit), but this does not exclude all H20 or all rational currents.
- The source is NOT a single Schiffer channel at the old marked point.
  `effective_schiffer.*` gives a stronger source-specific replacement
  `T_eff=N1/N0`, with an exact degree8 relative Jacobian identity.
  `effective_graph.*` gives its physical degree32,558-term graph.
  The degree10 product alone is weaker and can be automatic by character;
  the physical lift must retain Y2 denominators and all base derivatives.
- `round8/matched_ell/`: choosing the fixed Legendre j to equal the
  boundary elliptic factor is exactly compatible with the G/J elliptic
  pieces up to2-isogeny, but bounded targeted closure probes still have
  only exact kernels. Cycle now studies the smaller Chebyshev degree6
  slope cover and its varying elliptic quotient. The first partial
  normalization/minimal-line correction still gives zero mixed H20;
  remaining normalization corrections are being calculated.
- Eight-plane now also has a simpler global-Y cubic fiber with rank2
  tracezero residue algebra and exact source t^2/(2*C(t)^2), indexed in
  `round8/eight_plane_quartic/cubic_model.*`. Fresh is searching this
  current system. All six complementary coordinate 3+3 Euler supports
  containing X0 and excluding Y0 have now failed complete E2: coefficient
  rank742 and augmented rank743, with an exact rank upper bound supplied
  by35 global kernel vectors. This is a complex exclusion for these
  fixed supports, not an unrestricted exclusion.
  One moving-Segre cubic and its tau translate served only globally
  exact sources, so no target was obtained from that pilot.

- **Current constructive priority: rank5 marked-curve extension.**
  The proper rank3 connection omits the two actual-character residue
  directions on the moving divisor `t=s*h^2`. Add
  `sigma0=Res(h^4*Omega/((t-s*h^2)*C))` and
  `sigma1=Res(W^3*h*Omega/((t-s*h^2)*C))`. Their six simple residues are
  `-1/C_W` and `-W^3/C_W`; both forms are regular at infinity (orders4,1).
  Root, Cert and Reflection independently computed the same flat2x2
  residue connection. The boundary extension into the clean proper3
  is a19x21 weighted polynomial reduction. All8 boundary rows and all19
  coefficient equations now pass exactly; the complete5x5 system is flat
  over QQ for all6 direction pairs. Independent ordinary-form signs and
  finite-prime analytic jets also pass. See `round10/horizontal5/`.
  Reflection proved the third-kind theta projection is exactly
  `(1-zeta^2)*w^2*(v*sigma0-sigma1)`, with `v=-c*(1+s)-w^3`, and that
  its residue coefficient is horizontal. After the universal calculation,
  the physical pullback must include `s=T_eff` and all its derivatives.
  No rank5 source primitive or certificate has yet been obtained.
  The complete marked logarithmic tangent module is also free: four
  fields have Saito determinant21176820000*x*D1*D2*P*Q, where
  P=x*B(s), Q=49*x*Delta(s); all four full5 connection contractions
  are polynomial. Pullback currents must cancel their normal defects
  to the graph s=T_eff; Cert and Rank are implementing this exactly.
  `round10/effective_geometry/` records structured branch factors and
  the extra graph-indeterminacy divisor J. Fresh has identified the
  transverse normalization along the physical base curve as the
  canonical genus4 (2,3) cone, with R1O characters(1,1,3), a genuine
  nonrational singularity of the CONTRACTED finite model. The physical
  D32 retains this curve and is smooth there. Its global cone canonical
  jets interpolate exactly (45238 target slots from53668 sections), so
  the cone alone does not supply global H20. See global_twists/.
  The audited small radial-current modules also failed (90/91,270/271).
  They are bounded spaces, not unrestricted exclusions.

- Chebyshev degree6 normalization now has an explicit finite-flat order
  with basis `1,s,s^2,(s^3+a0*s/3)/r,u/r,u^2/(h*r^3)`, `r=h^2-4`.
  Every multiplication coefficient is polynomial over QQ[q,h] and all
  global bidegrees match exactly. Discriminant and codimension1 normality
  are being sealed. The normal-order cohomology vanishes in the tested
  minimal-line twist; isolated singularities and resolution corrections
  still prevent a conclusion about resolved mixed H20.
  **New nontrivial corner q=infinity,h=0:** its normalized exceptional
  base is the elliptic quartic yC^2=-v^4-6v^3+30v+9. The elliptic
  surface is a degree2 base change of a rational elliptic surface with
  twelve I1 fibers. Root independently checked squarefreeness, absence
  of branch/bad-fiber intersections and minimality; its true p_g is2,
  with explicit odd hol2 basis {1,v}dv wedge dx/(yC*yE).
  `round10/chebyshev_corner/` saves the independent calculation.
  These are forms on the exceptional surface. Their global extension,
  connecting map, and actual source-serving remain essential open tasks.
  Full minimal inverse module now has basis S*e0,e1,...,e5 after the
  O(2Dinf) correction, with weights(12,1),(4,2),(8,5),(12,6),(8,3),(16,3).
  Exact trace duals, rather than inverse basis weights, are required for
  corner filtrations. A tentative76-condition/rank75 shortage was an
  artifact of using the wrong trace-dual weights and is explicitly
  invalid as H20 evidence. Correct73-condition upper interpolation has
  full rank. Open finite base smoothness is now proved over QQ by a unit
  Jacobian ideal away q*h*(h²-4)*S; boundary chart completeness remains.

- **Current cyclic geometric priority: actual D32 boundary.** D32 has
  multiplicity17 along X0=X1=0 (Fermat sextic surface), and six generic
  split-node conductor surfaces Y1=0,Y0^6+Y2^6=0. The latter are sextic
  cones over the fixed genus10 curve; generic conductor and cone defects
  alone do not imply H20. At their collision with the Fermat boundary,
  Fresh and Reflection verified the actual weighted initial CI in
  variables(eps,W,b,r), weights(3,2,6,6), two equations degree12.
  It is quasismooth generically, has discrepancy-8 and local p_g10,
  with R1O characters(2,2,6). Relevant local adjoint jets are
  1,eps,eps²,b,r,W³. Cert computes their global twists/interpolation,
  Fresh the special-v degenerations, Reflection conductor transitions.
  Rank handles the collision Y0=Y1=Y2=0 (generic plane degree13 cone
  with six collinear nodes). No global serving class is proved.
  The source on Y2=1 near the Fermat center is exactly
  -a³*x⁴ dx wedge dv wedge dw wedge da wedge db/F²; first normal order4.
  Source symmetries cut these jets to{1,eps²,b,r}: globalY acts
  eps,W->-eps,-W, fixes the canonicalCIframe. Explicit degree32 global
  polynomial preimages span420 generic even jets; the full fine diagonal
  source character cuts this to140, still surjectively. This is generic
  interpolation, conditional on special-boundary adjoint restrictions.
  The six-conductor normalization generator theta has degree25, with
  quotient O_union(-25), union CI(1,6). Its raw H1/H2 corrections vanish
  by ACM and canonical restriction. Generic Gamma collision's degree13
  plane cone with six collinear nodes has an explicit normalization and
  full graded adjoint interpolation (31995 slots). Special-v loci remain.
  The main exceptional elliptic surface has chi13,pg12, but its coarse
  hol2 has wrong(mu3,Y) character; actual source lives in conormal layers.
  Initial-surface infinity bounds must NOT be used for the full germ:
  higher terms acquire negative powers and require further Newton charts.
  Fresh found another true infinity collision with adjoint ideal(u²,b),
  localpg2, defectbasis1,u. Sourcevanishingu³ alone is not a serving test.

- New complete fixed-support cyclic exclusion:
  D=X2^6+Y0^6+Y1^6+Y2^6. Full symmetry-reduced normalized E1/E2 has
  1248 columns, coefficient rank1236, augmented1237 mod1000003.
  Twelve independent exact universal homogeneous kernels provide the
  sharp QQ rank upper bound, so this is an exclusion over C. Root
  independently replayed it. Receipt `round10/fermat_cone_fixed/`.
  A second source-center Fermat cone has only a modular obstruction
  (rank1232/1233, four additional kernel lifts not yet proved).

- Off makes a fresh portfolio pass on four-plus-two-residual. Its core
  CY3 source lies in a symplectic-involution anti sector with H30=0,
  but no geometric coniveau theorem is yet available. Paired-ratio
  reduction again yields a cyclic genus4/Prym3 sector, so the invariant
  elliptic-density theorem does not automatically serve this source.
  A new genus7 signed-trigonal correspondence is exact and composes to
  4id on the desired Prym3; the simpler genus3 quotient loses the actual
  character. Its generic fixed-parameter surface still has antiH20dim2,
  so it is not a Fano contraction. Packet `round10/portfolio/`.
  Off now examines cycle-q2 using cached Discussion61 (already substantial
  fixed-parameter/Hecke obstructions); Reflection scouts the nontrivial
  Klein order7 character. No claimed easier target has emerged.
