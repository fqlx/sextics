Damped resultant formula for a complete ordinary trace
=====================================================

Status: a standalone characteristic-zero algebraic construction, independently
being audited. No actual low29/raw73 resultant coefficient has been evaluated.
This is not a primitive certificate or a computational feasibility claim.

Statement
---------
Let K be a characteristic-zero field and let F=(F1,...,Fn) be n polynomials in
n variables x=(x1,...,xn), with positive degree bounds di>=max(1,deg Fi). Assume
A=K[x]/(F) is finite etale. The zero algebra is allowed for the ordinary trace.
Let W in K[x] have total degree at most w, where w>=0. Put

    B=product_i di,       N=w+2.

Adjoin independent transcendentals a1,...,an,c1,...,cn and write L for the
resulting rational function field over K. Define

    G_i(epsilon,x)=F_i(x)+epsilon^B*(x_i^di-a_i),
    S(x)=sum_i c_i*x_i,
    H(epsilon,z,x)=1+epsilon*S(x)^N-z*W(x).

Homogenize G_i to degree di in x0,...,xn and H to degree N; the W term receives
the appropriate x0 power. Let

    R(epsilon,z)=Res(G_1^h,...,G_n^h,H^h) in L[epsilon,z].

Then R(epsilon,0) is nonzero. Let m be its order at epsilon=0 and let
r_m=[epsilon^m]R(epsilon,0), which is nonzero. All coefficients of
R(epsilon,z) have epsilon-order at least m and

    [epsilon^m]R(epsilon,z)/r_m = det_A(1-z*multiplication_by_W).

In particular

    Tr_{A/K}(W) = -[epsilon^m z]R(epsilon,z)/r_m.

Thus one needs an ALIGNED coefficient of R_z, not its own leading coefficient
if its order is greater than m. The result is independent of the auxiliary
a_i,c_i. For normalized trace, evaluate the same formula at W=1 to get
D=dim_K A, then divide the ordinary source trace by D, assuming A!=0.
One can use a common N based on a degree bound for an entire finite source pool.

Proof
-----
1. Before making the substitution t=epsilon^B, consider
   F_i+t*(x_i^di-a_i). The leading homogeneous forms in x are
   F_i,di+t*x_i^di. Here F_i,di means zero if the bound exceeds the actual degree. Their
   homogeneous resultant is not identically zero as a
   polynomial in t: its highest t coefficient is the nonzero diagonal
   resultant Res(x_1^d1,...,x_n^dn). Consequently they have no common
   nonzero zero over L(t). The affine complete intersection has length
   exactly B by Bezout.

   The a_i are generic target values for the finite polynomial map
   x -> (F_i+t*x_i^di)_i. Its Jacobian is not the zero polynomial; its top
   t coefficient is product_i(di*x_i^(di-1)), nonzero in characteristic0.
   Therefore the generic fiber, equivalently the system with independent
   a_i, is etale. It has B geometric roots. These assertions concern the
   generic t fiber; no good fiber or no-infinity assertion is made at t=0.

2. Work over an algebraic closure of K(a_i) and use the t-adic valuation,
   normalized by v_t(t)=1. Every individual root lies in a finite extension
   of the completed Laurent-series field of degree at most B. Its ramification
   index e is at most B. If some coordinate has a pole then

       M_t=-min_i v_t(x_i) >= 1/e >= 1/B.

   After t=epsilon^B, compatible valuations are multiplied by B. Thus every
   escaping branch has M=-min_i v_epsilon(x_i)>=1. This argument does not
   require that every e divide B; a denominator bound, rather than integral
   exponents, is sufficient.

3. Every branch whose coordinates all have nonnegative valuation reduces to
   a geometric zero of F. Since A is finite etale, each such zero is simple
   and Hensel's lemma gives exactly one lift. There are no additional bounded
   branches reducing to the same zero. Thus bounded branches correspond to
   every factor of A, without a selected-factor or component omission.

4. The roots of G do not depend on the c_i. Their independence makes
   v_epsilon(S(x))=-M at an escaping branch: its lowest-coordinate terms
   cannot cancel in a generic linear combination. Polynomial degree gives
   v_epsilon(W(x))>=-w*M. Since N=w+2 and M>=1,

       v_epsilon(1+epsilon*S^N)=1-N*M<0,
       v_epsilon(W/(1+epsilon*S^N))
           >=-w*M+N*M-1 = 2*M-1 >=1.

   Every escaping contribution therefore vanishes in the residue field.
   At a bounded branch the damping factor is a unit with residue1, and its
   contribution reduces to W at the corresponding original zero.

5. The Poisson product formula for the projective resultant, using the fact
   that G has no zeros at infinity over L(epsilon), gives

       R(epsilon,z)/R(epsilon,0)
         = product_over_B_roots(1-z*W(x)/(1+epsilon*S(x)^N)).

   All factors have coefficients of nonnegative epsilon valuation. The
   escaping ones reduce to1 and the bounded ones reduce to1-z*W(x0).
   Reducing the product proves the stated characteristic-polynomial identity,
   and its z coefficient proves the ordinary trace formula. Trace base change
   identifies the answer with the K-valued trace of A.

Localization and the complete etale locus
-----------------------------------------
The statement requires a finite etale polynomial algebra, not a finite list
of observed roots. If the input is a square system E(y)=0 and source formulas
invert functions u_j(y), first introduce variables v_j and equations
v_j*u_j(y)-1. If finiteness/reducedness of the intended complete locus is not
otherwise certified, also introduce v_J with equation v_J*J_E(y)-1, where
J_E is the full square Jacobian determinant. The resulting finite-type
algebra is zero-dimensional and etale (or zero), hence finite. The augmented
Jacobian determinant is J_E^2*product(u_j), up to the displayed block ordering,
so all of its geometric zeros are simple. Rational sources become polynomial
by replacing every inverse with its variable. Apply the statement to this
ENTIRE augmented square system and the degree bound of that polynomial source.
All field factors of this explicitly localized algebra are counted.

This does not prove the localization is nonzero, that it contains every factor
wanted in some other geometric construction, or that an arbitrary selected raw
field equals it. Those are separate obligations. In particular, a pivot chart
must not be called the complete original incidence algebra without a coverage
proof. The formula solves escaping-root bookkeeping for a specified finite
localized algebra; it does not infer selected-factor identities.

Computational assessment
------------------------
The formula avoids F4, a primitive element, and a finite quotient basis in its
DEFINITION. It does not make the required resultant small. Computing only its
initial-epsilon polynomial (and only the linear-z part) is much cheaper than
expanding the entire resultant in principle, but no bounded method has yet
been demonstrated for the contact systems.

Already the unsaturated low29 core has degree list 25x6,2,3,2,7, hence the
classical deformation rank B=84*6^25 (~2.39e21). Adding one geometric inverse
and a full-Jacobian inverse increases the degree product substantially. The
raw73 core has68degree2,2degree1,2degree3 and1degree4 equations. Its full
Jacobian has degree<=75; adding a Jacobian inverse gives74variables and
B=807524668570709331542016. The source pool has a safe polynomial degree
boundw=92 (degree5 coefficient forms, degree68 cofactors, degree18 source
factors and one Jacobian inverse), soN=94. A classical dense Macaulay
resultant matrix has degree244 and about4.45e73 monomials. These concrete
bounds are saved in damped-raw73-size.json. Therefore a dense Macaulay matrix,
box-basis trace computation, or enumerating all B branches is infeasible.
The realistic implementation would need a sparse initial-resultant or block
factorization computation that uses the norm/gauge structure, with a checked
certificate for its initial coefficient. No such computation is claimed here.

One must not expand the damping inverse geometrically term by term after
quotient reduction: it is not small on escaping branches. The resultant ratio
or an equivalent exact rational inverse is essential. Likewise, setting
epsilon=0 before removing the common epsilon factor of the resultant is invalid.

Exact toy receipts
------------------
Script damped_trace_toy.py tests G=epsilon^2*x^2+x-1, W=x^m for m=0,...,4,
with damping1/(1+epsilon*x^(m+2)). The root tending to1 contributes1 and the
root of order-epsilon^-2 contributes0; the resultant logarithmic derivative
has constant term1 in every case. Results: damped-trace-toy.json. This is a
sanity check of the mechanism, not a contact-source or completeness certificate.

Primary reference background
----------------------------
Poisson resultant/global-residue methods: Cattani-Dickenstein-Sturmfels,
Computing Multidimensional Residues, https://arxiv.org/html/alg-geom/9404011.
The damping/valuation separation above is the present explicit construction;
it is not being attributed as a theorem proved in that reference.
