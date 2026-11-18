# The critical cone cannot support the primitive Cycle Q2 class

Write (a,b,c,d,q,y)=(X0,X1,X2,Y0,Y1,Y2). Let X be the supplied sextic fourfold. Its non-diagonal terms are m=a³bdq/2, n=b³cqy/2 and u=c³ady/2. Write W=V(C) for the critical divisor of the three-parameter change of variables in the single-holomorphic-form reduction, with V the log vector (5,4,19). In the torus model its equation is τ³(b₀³+14T²−5)=3T. On the chart c=1, τ=ad, b₀=b²/a² and T=(d/a)³. Its closure in X is thus D=X∩Z, where

    H=−5a⁶+b⁶−3c⁶+14d⁶,     Z={H=0}⊂P⁵.

Let S={H=0}⊂P³. The singular locus of the projective cone Z is the vertex line ℓ=[q:y]. We prove below that D has exactly six singularities, the six roots of q⁶+y⁶ on ℓ. All are ordinary cones over the smooth diagonal sextic surface S in the analytic sense. The Gysin image of classes supported on D in H⁴(X,Q) is contained in Q h². This also excludes D together with arbitrary orders of coordinate poles as the sole support of the nonzero primitive class surviving on the ordinary sextic torus. The current used in the one-form reduction itself uses other denominators, including F_Y. This support result does not rule out primitives using other divisors.

## Exact transversality over a finite field

We test outside ℓ over the algebraic closure of F₁₀₀₉. As S is smooth, any failure of transversality gives dF=λdH. Write (A,B,C,D₀,Q,Y) for the six sixth powers and h=(−5,1,−3,14). The logarithmic equations, valid also when coordinates vanish, are

    6(λ h_i−1) (A,B,C,D₀)_i = (3m+u, m+3n, n+3u, m+u)_i
    6Q=−m−n                  6Y=−n−u.
    h₁A+h₂B+h₃C+h₄D₀=0.

The cross terms satisfy

    64m⁶=A³BD₀Q,      64n⁶=B³CQY,      64u⁶=C³AD₀Y.

If (m,n,u) vanishes, so do Q and Y. For λ≠0 at most one base sixth power could be nonzero since the four h_i are distinct. The remaining H equation then kills it. The case λ=0 is immediate as well. It thus suffices to consider [m:n:u] in P².

For λ≠0 write d_i=λh_i−1, W_i=∏_{k≠i}d_k. Write g_{ij} for the 4-by-3 coefficient matrix in the first displayed system. The resulting linear relation L·(m,n,u)=0 has

    L_j=(Σ_i h_i W_i g_ij)/λ.

These are polynomials of degree at most two. Their gcd is 1. On the chart L_j≠0 solve the relation by putting the two free coupling values equal to L_j times binary coordinates, and substituting for the j-th value. Each numerator Σ_k g_ik m_k is then polynomially divisible by d_i. This recovers the four scaled base sixth powers, including at the simple zero of one d_i. At such a zero, the i-th base value occurs only in H and is uniquely determined by that equation. The expression obtained by polynomial division gives that value by the polynomial identity H=0. With Q,Y also recovered, the three sixth-power identities above become binary sextics homogeneous in the two free variables. Each coefficient has λ-degree at most twelve.

The three pairwise homogeneous resultants are 12-by-12 Sylvester determinants of λ-degree at most 144. The replay evaluates each determinant at 145 field elements, interpolates by forward differences and checks a 146th value. For each chart it takes the gcd of the three resultants. At p=1009 these gcds are

    (λ+673)³⁶(λ+743)³⁶,  (λ+72)³⁶(λ+202)³⁶,  (λ+892)³⁶(λ+1008)³⁶.

In fact each gcd is supported exactly on the zero set of its chart minor. No nonzero λ can produce a singular point. For λ=0 substitute the Euler identities without denominators into the three sixth-power relations in m,n,u. Their homogeneous multiples in degree 16 span all 153 degree-16 monomials, so there is no projective solution. The test also passes independently at p=1013.

To pass to characteristic zero, blow up the vertex line of P⁵ and restrict this P² bundle over P³ to the smooth surface S. On this smooth projective fourfold the pullback of X is a projective family of plane sextics over S with a nonzero leading coefficient of q⁶, so it is a relative Cartier divisor flat over Z localized at 1009. On the exceptional divisor S×P¹ its equation restricts to q⁶+y⁶=0 and has simple roots. Hence the strict transform is smooth along the exceptional divisor in that characteristic. The resultant check establishes smoothness on its complement. Properness and openness of smoothness now give smooth generic fibre. On complex X at each vertex root one can solve the smooth original sextic equation in the ℓ direction. The other four coordinates give a chart in which D has equation H(a,b,c,d)=0 exactly.

## Cohomology with support

The open stratum Z°=Z minus ℓ is the total space of a rank-two vector bundle over S. Put D°=D minus the six singularities and X°=X minus the same points. The cone has a Whitney stratification by Z° and ℓ, locally the product of a smooth curve with the affine cone on S near ℓ. The Veronese embedding of degree six makes the section F=0 a hyperplane transverse to both strata. The Goresky–MacPherson weak Lefschetz theorem (Intersection Homology II, Theorem 7.1) gives an isomorphism IH²(Z)→IH²(D). This restriction agrees with ordinary restriction on the open strata. Both deleted strata have complex codimension three. Therefore the unshifted middle intersection complexes are τ≤2 Rj_*Q from their open strata, and their degree-two hypercohomology equals ordinary H² of those strata. In particular H²(Z°)→H²(D°) is surjective.

Transversal base change for the Gysin map in the smooth ambient space P⁵ minus ℓ sends each such restricted class into the restriction of H⁴(P⁵ minus ℓ)=Q h². Removing six points preserves H⁴(X); removing the line from P⁵ preserves H⁴(P⁵). The kernel of H⁴(X°)→H⁴(X° minus D°) is exactly this Gysin image by purity and the localization sequence.

For the coordinate torus U of X the intersection D∩U is smooth. If a weight-four class of H⁴(U) lies in the Gysin image from H²(D∩U)(−1), strictness for the weight filtration supplies a preimage in W₂ H²(D∩U). Every such class comes from a smooth proper compactification, for example the strict transform described above. It therefore restricts through H²(D°). Its Gysin image lies in the ambient span, which restricts to zero on the coordinate torus. Thus every nonzero weight-four class on U survives deleting D∩U. In particular this applies whenever the independent proof of survival for the protected numerator on U is used.

Sources: Goresky and MacPherson, [Intersection Homology II, Section 7](https://www.maths.ed.ac.uk/~v1ranick/papers/gormac2.pdf). For the lowest-weight compactification characterization see Peters and Saito, [Lowest Weights in Cohomology of Variations of Hodge Structure](https://arxiv.org/abs/0708.0130).

## The lines on S

The 108 standard lines on the sextic Fermat surface S impose two scaled proportionalities pairing the four base coordinates. At an endpoint just one pair of coordinates is nonzero. Choose the endpoint whose active pair differs from {b,c}. All three couplings vanish there. The fibre is q⁶+y⁶+κw⁶=0, where κ≠0 because the two active diagonal coefficients of H are distinct. Thus the surface cut out on X by each pair of hyperplanes has an integral hyperplane section in P³ and is itself integral. None of the 108 inverse images splits. Every one of these surfaces has cycle class h².

## Replay

Use Python with python-flint. The program takes well below one second after import on the development computer.

    python cone_sing.py
    python cone_sing.py --prime 1013
