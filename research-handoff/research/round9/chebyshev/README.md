# Chebyshev degree-six cover: exact normalization and remaining resolution work

This folder is research outside the protected repository. There is **no off-paired certificate** here.

## Exact maps and actual source

`verify_model.py` checks both degree-three elliptic quotient maps, signs, relative differential factors, and the slope sextic. In particular the second map is

```
R=(k³−4τ)/(k²−4), Y=(k³−12k+8τ)Z/(k²−4)²,
x=sR, y=Y,
y²=x³−27s²x−27c0, dx/y=s*k*dk/Z.
```

It keeps exactly the `k dk/Z` elliptic factor. The first quotient keeps `dk/Z`. There is no square-root of the slope in the second quotient.

`source_jet.py` differentiates the slope equations using the **actual** λA deformation of the physical K3, with the stored physical coefficient jets. The projected second elliptic family varies nontrivially: an exact witness in the irreducible degree-six extension at p173,q2,h14 has nonzero sλ, τλ and jλ. This does not itself identify a Gysin image.

## Normal finite-flat degree-six algebra

Let r=h²−4, u=b2/s. The slope equation is

```
9s6+3a0s4+3b1s3+a1*b2*s+b2²=0.
```

The following basis gives an exact global finite-flat normal algebra over P1q×P1h:

```
e0=1,
e1=s,
e2=s²,
e3=(s³+a0*s/3)/r,
e4=u/r,
e5=u²/(h*r³).
```

The pole bidegrees are

```
(0,0),(4,3),(8,6),(12,6),(8,4),(16,4).
```

`normalize_explicit.py` checks every multiplication entry is in QQ[q,h] and its separate q/h degrees fit these weights. `normalized_algebra.pickle` stores all six multiplication matrices and the basis change from the first partial order.

`discriminant_check.sing` computes the exact trace discriminant. It is a nonzero rational constant times

```
h²*(h²−4)²*(54(1+q6)²h−q³)*R(q,h),
```

where R is irreducible over QQ, has bidegree (84,35), has q-content 1, and is squarefree over QQ(q). The full factorization is replayed by the script; the large polynomial is in `residual_branch.txt`.

Normality follows from CM plus R1. A simple discriminant factor permits no larger integral order. At h0 and each r0, the raw Newton polygon has four small roots of valuation1/2 and3/2 respectively, hence two ramification-index2 branches; the discriminant exponent2 is minimal. At h∞, the two index3 branches have s~h^(8/3), hence minimal discriminant exponent4. The weight sum gives degree46 in h while the affine discriminant has degree42, exactly exponent4 at infinity. At q∞, s~q4 with six distinct leading roots; the discriminant has its full qdegree96, so this divisor is étale. These checks cover all codimension-one divisors. Irreducibility is witnessed at p173,q2,h14, where the monic slope sextic is irreducible.

Normality does **not** mean the cover is smooth, nor that its resolution has the same coherent cohomology.

## Minimal elliptic line on the normal cover

Write L0=π*O(2,2). Generically on S=54J²h−q³=0 there is one bad branch, s uniformizing and t of pole order1. It requires +Dbad in the fundamental line. Over h0 and r0, t is generically finite and no bad twist is required. At h∞ the original coefficients have valuations A8,B12 on each of the two index3 branches, so subtract2D∞. Thus the divisorial minimal line is

```
Lmin=L0+Dbad−2D∞.
```

`minimal_line_module_check.json` checks the exact module action for O(2D∞), with weights

```
(0,0),(4,2),(8,5),(12,6),(8,3),(16,3).
```

After tensoring O(−2,−2), every summand has both degrees negative, so H1 vanishes on the normal base before the Dbad ideal. Restricting to the bad curve cannot add H0: its map to S has degree1; O(−2,−2)|S has degree−26, and the 2D∞ allowance contributes at most2 at each of the six J roots, still negative. A complete write-up should express this with the rank-one torsion-free restriction, rather than treating Dbad as globally Cartier without proof.

The essential unresolved issue is resolution and further minimality at isolated corners.

## Nontrivial q∞,h0 corner

The weighted blowup chart has a particularly simple physical expression:

```
q=1/Q, h=Q6 H, original s=S, original t=T.
```

All transformed a_i,b_i are polynomial in Q,H. At Q0,

```
a1=24H, a0=−1/243, b2=432H²,
b1=−40H/27, b0=−H²/64−2/19683.
```

The main exceptional base curve is

```
9S6−S4/81−(40/9)HS3+10368H3S+186624H4=0.
```

Its normalization has genus1, checked exactly by `corner_qinf_h0.sing`. Put v=108H/S and yC=81S. Then

```
yC²=−v4−6v3+30v+9,
H=v*yC/8748, T=−2v/27−v²/81.
```

The second elliptic surface is a degree-two base change of a rational elliptic surface over v. Parent independently verified all discriminant/minimality facts in `/workspace/research/round10/chebyshev_corner/elliptic_basechange.py`: its fundamental line has degree2 and p_g=2. Two forms are proportional to

```
{1,v} dv∧dx/(yC*yE).
```

Both are odd under yC→−yC and yE→−yE. They are local exceptional forms; global extension remains essential.

`blowup_qinf_h0.py` checks the full Q-chart finite algebra and the next singular point's initial model. At Q=H=S0, use weights Q1,H3,S3. The initial coefficients are

```
a1=24H, a0=−1/243,
b2=432H²−8HQ³, b1=−40H/27, b0=−2/19683.
```

Its rational exceptional base is parametrized by T:

```
s/H=−72(81T−5)/[(27T−1)(27T+1)],
Q³/H=54(9T−1)(59049T³+6561T²−1053T+19)/[(27T−1)²(27T+1)²].
```

The associated elliptic exceptional surface is the rational elliptic surface

```
y²=x³−27(27T−2)(27T+1)²/19683
```

with fibers II, IV, I0*. This identifies the next leading component but is not yet a full strict-transform singularity classification.

## Explicit connecting-map setup

`corner_canonical_generators.py` computes the exact fiber algebra at q∞,h0. Its canonical module has type3, generated minimally by trace-duals e3*,e4*,e5*. These generators extend as global canonical sections after the minimal-line infinity correction: multiply by h0² to impose the required vanishing along D∞. Available Q-jet budgets are12,8,16.

For local function weights [0,4,8,12,8,10], the canonical weights after the elliptic line correction are5−w_i. Thus the candidate forbidden jets satisfy

```
j+6k <= w_i−5.
```

For the three generators these are Q^0..7 plus H*Q^0..1; Q^0..3; and Q^0..5. Every one fits the explicit global budgets. If the normalized strict transform has only rational/quotient corrections beyond the displayed main exceptional surface and the rational next surface, this gives a direct global canonical-section surjection onto the local adjoint defect, killing the possible new global H20 from this corner. That geometric adjoint comparison has not yet been fully proved, so no exclusion is asserted here.

Other isolated corners, especially J0,h∞ and q∞,r0, also need a complete inventory before any global resolved-H20 claim.

### Strict-transform Jacobian replay

`chart_singularity_slice.py/.sing/.log` constructs the Q-chart order using u=b2/s and v=u²/H, and computes its full codimension-three Jacobian minors on Q0. Saturating H gives the unit ideal over QQ. At H0 its singular support is exactly s=u=v=0. Thus there is only one affine base singular point on this exceptional curve, the next weighted model displayed above. This is stronger than a point sample, but the remaining weighted charts and the canonical-adjoint comparison must still be included in a complete resolution argument.

### Next weighted initial base is rational

`next_initial_normality.sing/.log` checks the six initial relations with ga=432H−8Q³. Their full Jacobian ideal saturates Q and H to units; their only singular point is the vertex. The rank-four small-branch order is free over QQ[Q,H] with basis1,s,u,v and Hilbert series `(1+3t³)/[(1−t)(1−t³)]`. Its canonical module has only positive weights, so this normal graded surface singularity is rational. The actual next chart is a higher-weight deformation of it. A full argument should cite the standard preservation of rationality under this filtered degeneration, then handle the total elliptic model (the leading exceptional elliptic surface is the RES already displayed).

### Two infinity charts of the genus-one exceptional curve

At the first weighted blowup, use the h-chart with ε=h^(1/6), qtilde=Q/ε and s'=ε⁴σ, x'=ε⁴χ, y'=ε⁶ψ. The two normalized C∞ points have S~v²,H~v³, hence qtilde~v^(−1/2). The residual stabilizer is μ2, acting `(ε,qtilde)→(−ε,−qtilde)` and fixing the good elliptic fiber coordinatesχ,ψ. Thus the remaining singularity is A1 times a smooth elliptic fiber. Its resolution is crepant and adds ruled surfaces. This gives no extra adjoint condition for a reflexive canonical form already regular on the normalized first weighted chart. It avoids relying on an unverified integral conormal degree: the weighted conormal initially is a Q-line and naive thickening dimensions may require rounding.

## J0,h∞ leading chart and possible adjoint interpolation

`J_corner_leading.py/json` verifies the leading component after j=J=ε³, z=1/h=ε⁶B. There are two choices T=±iS, with τ=±i and constant elliptic j=6912/5. The slope satisfies

```
S³=−(delta*B−54)/(24*eta*B8), delta²=eta²=−1.
```

After U²=S and x=54/(delta*B), V=U/x, the twist curve is V⁶=C*x(1−x), genus2. The index-three deck acts V→omegaV and fixes the constant elliptic coordinates X/S,Y/U³. Its curve quotient is a conic. Thus reduced leading Hol2 is killed by this trace, but character-shifted conormal thickenings are not excluded by that observation.

`J_corner_adjoint_budget.json` records a direct affine trace-dual weight calculation. The original e_i have ε-weights [0,−14,−28,−30,−16,−14]; dq∧dh hasweight−3 and original dx/y hasweight7. The maximal allowed global h powers are [0,2,5,6,3,3], obtained by dualizing the exact minimal-line inverse module. The resulting minimum canonical weights are [4,6,2,−2,2,0]. Hence only e3* h6 and e5* h3 can be nonregular at the leading exceptional valuation, and one factorJ makes both regular. Their q-degrees12,16 are sufficient to interpolate separately at the six J roots. This remains a candidate global adjoint comparison: the normalized strict-transform charts and possible additional exceptional valuations must be audited before using it as a theorem.

## Full Dbad ideal module (exact, replaces the earlier restriction-degree shortcut)

`bad_ideal_module.py/json` proves that evaluation of N=O(2D∞) on the bad branch is the global A-linear map e0→1 and all other e_i→0 on S. Every constant row in multiplication by a nonconstant algebra basis element is divisible by S. Its kernel has exact global free basis `{S*e0,e1,...,e5}`, and is CM/reflexive; since it agrees in codimension1 with N(−Dbad), it is the required divisorial ideal module.

Consequently the FULL minimal-line inverse pushforward splits with degrees

```
(-14,-3),(-6,-4),(-10,-7),(-14,-8),(-10,-5),(-18,-5).
```

Normal-base H1 is therefore exactly zero without any argument about the degree of a restriction to Dbad. Duality gives the FULL global canonical coefficient budgets

```
(12,1),(4,2),(8,5),(12,6),(8,3),(16,3).
```

The extra generator omitted by the earlier pre-Dbad calculation is e0*/S, budget(12,1). It potentially adds Qjets0..1 at the main q∞h0 corner and one constantJ jet at each J0,h∞ corner. These must be included in a complete adjoint argument.

`global_adjoint_interpolation.py/json` checks all proposed upper boundary jets simultaneously over QQ, including that extra generator. There are73 conditions and every block has full row rank:8,2,17,26,6,14. These constraints include q0h0,q0h±2,q∞h0,q∞h±2,J0h∞. This establishes that there is no global interpolation shortage for these proposed local spaces. It does **not** establish that the proposed weighted spaces exhaust the geometric adjoint defects: full normalized-corner/strict-transform completeness is still the essential obligation.

## Correction: the apparent one-dimensional RES interpolation shortage is false

`trace_duals.py` computes the actual field trace-duals, with f the monic slope sextic:

```
φ0=s²(a0*s+b1+3s³)/(3f_s),
φ1=s4/f_s,
φ2=s3/f_s,
φ3=r*s²/f_s,
φ4=−r(a1*s+b2)/(9f_s),
φ5=−h*r³*s/(9f_s).
```

This calculation invalidates the shortcut that a trace-dual's valuation is always the negative of its basis element's valuation. At the next RES chart, f_s hasweight9 and φ2 hasweight0. Consequently that chart imposes no stronger condition than the main exceptional surface. At q0h0 every actual canonical weight is positive, so no adjoint condition comes from that generic valuation at all.

`global_adjoint_with_RES.*` is retained as an arithmetic record but **marked INVALID as a geometric obstruction**: its20/19 block used the wrong filtration. The apparent q² source coincidence therefore gives no evidence for a certificate. `actual_dual_weights.py/json` records the corrected actual-dual table. The original73-condition full-rank interpolation is conservative for the corrected generic valuations.

## Further finite-boundary inventory

`open_base_jac_QQ.sing/log` proves exact QQ smoothness of the raw slope surface on q*h*r*S≠0: the saturated full Jacobian ideal is1. `S_nonzero_s_base_jac_QQ.sing/log` proves the same on S0,s≠0,qhr≠0. At S0,s0 the two partial-order branches are directly smooth by the su=b2 relation and the unit a1. Thus no unknown finite nonboundary base singularity remains.

At generic h0 on the t0=−1/27 branch, put h=ρ² and s=ρσ. Then σ²=−72q³ and

```
t=t0+ρτ1+…,
τ1=(9q4−64J)/(6σ),
c0=−τ1²ρ²/9+… .
```

The a0t0+b0 terms of first order in h cancel. Hence the IV-fiber coefficient enhances at the six roots of9q4−64J. The base is smooth there. The Weierstrass x coefficient has a unit timesρ², so a general transverse surface section has a D-type rational double point; this supplies the standard cDV/canonical argument for the total threefold at those finite enhancements. It must be included explicitly rather than assuming a generic IV fiber at every h0 point.

At finite S∩r points q³=±108J², the local weighted balance is r1,S1,s2. The actual trace-dual canonical weights are positive (φ2 contributes2, φ3/4/5 contribute1, extraφ0/S contributes1); its leading exceptional elliptic surface is another rational elliptic surface over the t-parameter. A precise normalized completion argument is still needed for a polished global proof.
