# Boundary component inventory (reduced supports)

This separates verified reduced-support models from the still unfinished
resolution/adjoint calculation. It does not assert a complete irregularity
theorem for the main component.

In the affine base chart write `r=h²-4,J=1+q6`. A residual surface means a
component of the raw CI removed by saturation; generic multiplicities and
their embedded intersection schemes require separate bookkeeping.

| Boundary support | Birational normalization / irregularity data |
|---|---|
| v=0,h=0 | P1_q times E0, with E0 the normalization of U6=-(t+1/27)²(t-2/27)/(4ell); genus1,j0 |
| v=0,h=+2 or -2 | weighted sextic surface T³-(h/32)q*T*z³-(q6+z6)/16+4ell*V6=0 in WP(1_q,2_T,1_V,1_z); quasismooth, hence irregularity0 |
| U=0,h=0 | two rational sections t=-1/27,2/27 over (q,v); the first has nonreduced generic structure |
| U=0,h=+2 or -2 | C4_h times P1_v, where C4_h: T³-(h/32)q*T*z³-(q6+z6)/16=0; smooth genus4 |
| v=infinity | section U=t=0, rational over (q,h); isolated generic primary length90 in cycle's exact modular probe |
| z=0,v=0 | three fixed fiber points t³=-4ell*U6, rational over (q,h) |
| h=infinity,v=0 | three rational ruled components t=constant*U² over q |
| h=infinity,U=0 | t=0, rational over (q,v) |

The transformation for the two weighted sextic surfaces is t=q²T,U=qV,
away from q=0. Quasismoothness reduces to that of C4_h because the V
derivative forces V=0. `C4_smooth.sing/.log` gives the exact good-prime
weighted-cone Jacobian calculation (dimension0), which by projectivity
also verifies characteristic-zero quasismoothness. The only singular
point of the ambient weighted projective space is not on the hypersurface;
alternatively quotient singularities have rational resolutions. Thus their
resolved irregularity is zero.

At finite nondegenerate (q,h), fixing a finite nonzero v cannot leave a
curve in the weighted projective fiber unless b2=a1=0. Indeed set U=1 on
the dense fiber chart and write E1=l*t+m. The t-resultant of E1,E2 has
z^12 coefficient 3v*b2². If b2=0, the t-resultant of E1,E3 has z^12
coefficient -(a1*v)³. Therefore a positive-dimensional fiber forces
h*r=0: a1=(3/2)h*r²*J and b2=h*r³(q³-54hJ²)/8 have no other common
finite-base zero. Fiber curves contained in U=0 or z=0 are excluded by
the monic t³ equation. The degenerate v²=1,ell cases have empty generic
fiber, verified exactly at q2,h5,F109 in `../projective_model/degenerate_v_mod109.sing`.
Consequently these v values create no additional residual surface away
from the h=0,+2,-2 levels.

When all physical coefficients vanish, as at z=0 or the h=infinity
leading model, there is no solution with U*v finite nonzero. Set U=1 and
V=v². E1 forces t=-(V+1+4ell)/3; the two other equations have resultant
`-4096*(ell-1)^6/729`, a nonzero constant. This exact calculation is
`cube_exclusion.json`. The remaining U/v boundary strata give the rational
components listed above.

At q=infinity, h=5, the U*v-nonzero fiber has dimension0 and length48
in the exact modular probe `q_infinity_h5.sing/.log`. Boundary U/v/z
charts are also zero-dimensional there, so the proper projective fiber
is zero-dimensional. This rules out a q=infinity residual surface
dominating h. At fixed h away 0,+2,-2,infinity, E2 imposes a nonzero
quadratic equation in t/U² while E1 has a nonzero z6 term, excluding a
two-dimensional fiber. The exceptional h levels are covered by the
listed strata. This is a reduced-support argument; it does not compute
the primary multiplicities at their intersections.

## Main-component exceptional / conductor curves already verified

| Locus | Normalized curve / needed odd H1 |
|---|---|
| q=0, selected boundary branch | j0 elliptic, odd |
| q=infinity, selected boundary branch | same j0 elliptic, odd |
| each of24 roots of P=11664J4-q6 | rational exceptional component through C; explicit parametrization in P_exceptional_rational.json |
| each of24 roots of G | elliptic conductor, j54000; useful odd normalization layers are being matched globally by cycle_geometry |
| each of6 roots of J, h=infinity | genus7 exceptional curve y6=-4(1+v²)[ell+(ell-1)v²]; its odd Jacobian is isogenous E0^4, see J_exceptional.py/.json |

The h=+2 and h=-2 genus4 curves are isomorphic by q->-q. Their order-three
automorphism has elliptic quotient Y²=X³+X²/16-4, whose j is
`-1/(256*110591)`, plus a three-dimensional Prym. The elliptic quotient is
not geometrically isogenous to the elliptic factor of the genus11
boundary curve: at prime5 the ordinary endomorphism fields are
Q(sqrt(-19)) and Q(i), respectively. Rank_candidates is separately
auditing the Prym factor.

## Remaining gaps before a Hodge-subquotient exclusion

The table is not yet a complete list of exceptional curves in a resolution
of every corner or isolated singularity. In particular the smooth finite-
base moving-quotient open still needs a complete main-component
normality/singularity check; a capped Jacobian-minor computation is only a
probe. Intersections of residual components and their main-component
conductor maps also need exact normalization or local models. One must
exclude additional positive-genus resolution curves, and prove the
normalization/resolution exact-sequence subquotient statement with all
those strata included, before concluding that no non-CM boundary factor
extends globally. Raw-CI H1=0 alone does not provide that conclusion.
