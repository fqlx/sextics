# The three original Y-polar divisors have trivial weight-four support on the torus

Continue with (a,b,c,d,q,y), X, the sixth powers A,B,C,D,Q,Y, and the three coupling monomials m,n,u as in FERMAT_CONE_SUPPORT.md. Write U=X∩(C*)⁵ for the projective-coordinate torus section. On this torus the q-polar equation ∂F/∂q=0 can be written as P=6Q+m+n=0. The ambient polar V is isomorphic to (C*)³ times the affine line punctured at two points. Indeed normalize q=1, take a,b,c as free torus coordinates, and take s=m/Q and t=n/Q as the two remaining independent characters up to constants. The exponents of d,y in these last characters are the unit matrix. Then t=−6−s. The Hodge structure H²(V) is pure of weight four.

We claim restriction H²(V)→H²(V∩U) is an isomorphism. First establish transversality to all Newton faces of the pair (P,F). For an arbitrary real weight vector, let I be the coordinates of least weight (this definition is independent of a common shift). The initial form F₀ consists of the pure sixth powers of the coordinates in I and those coupling monomials supported completely in I. The initial P₀ is a nonempty sum of some of 6Q,m,n.

All these face polynomials F₀ are smooth on their zero-locus in the torus. Indeed, if their logarithmic Euler derivatives vanished, putting all coordinates outside I equal to zero would give exactly the six Euler equations with λ=0 in cone_sing.py, also satisfying its three sixth-power identities. Its homogeneous Macaulay matrix is surjective in degree 16 modulo 1009. Therefore it is surjective in characteristic zero, excludes any projective [m:n:u] and then forces all six powers to vanish. All the faces of P are smooth since its three exponents are affinely independent.

If P₀ is a monomial its zero-locus is empty. Otherwise consider the following cases on P₀=F₀=0.

* If q belongs to I, then 6Q belongs to P₀, and the remaining terms in P₀ occur precisely when their supports are contained in I. Thus q∂q F₀=P₀=0 and q∂q P₀=30Q. The forms meet transversely.
* If q does not belong to I and 6Q belongs to P₀, F₀ is independent of q, and q∂q P₀=30Q still holds. This gives transversality.
* Otherwise P₀=m+n and q does not belong to I. At a zero, the logarithmic gradient of P₀ is a nonzero multiple of v=(3,−2,−1,1,0,−1) in coordinate order (a,b,c,d,q,y). Unless I consists of all five non-q coordinates, some coordinate outside I has v_i≠0 and F₀ is independent of it. This again yields transversality.
* In the remaining case F₀=A+B+C+D+Y+u. A failure of transversality gives, for a scalar t obtained by dividing the gradient multiplier by u,

      6(A,B,C,D,Y)/u = (3t−1,−2t,−t−3,t−1,−t−1).

  As 64u⁶=C³ADY and A³D=B²CY follows from m+n=0, the two univariate polynomials below must vanish simultaneously.

      64·6⁶−(−t−3)³(3t−1)(t−1)(−t−1)
      (3t−1)³(t−1)−4t²(−t−3)(−t−1)

  Their exact integer resultant is 11734509093199349943633020232663040.

The complete intersection of P and F is therefore nondegenerate on every face, including its dense torus. To compare it with a generic section, choose a smooth projective toric compactification from a common refinement of the normal fans of the two Newton polytopes. On each toric orbit the restrictions of the equations are, up to units, the initial forms in that normal cone. The compactified polar is smooth with a simple normal crossings boundary and the compactified sextic section is transverse to each of its boundary strata. For clarity, the sextic hypersurface is allowed to vary in the full space of degree-six homogeneous forms while P stays fixed. The subset with nonzero vertex coefficients and transverse intersections on all the finitely many boundary strata and the open stratum is Zariski open; properness of the compact stratification supplies openness. It is nonempty by the preceding test. The compactified pairs above this connected open subset are topologically locally trivial by the proper stratified isotopy theorem, including the inclusion of the open polar sections in V. For a general sextic in the same family, use the sixth Veronese embedding of the original P⁵, applied to the smooth four-dimensional quasi-projective V, and the quasi-projective Lefschetz theorem of Hamm and Lê, Theorem 1.1.3. Thus V is obtained up to homotopy from its general section by attaching cells of real dimension at least four, and the degree-two restriction map is an isomorphism. Local triviality gives the same isomorphism for the specified coefficient vector. The restriction map is algebraic, hence an isomorphism of mixed Hodge structures.

Consequently the smooth divisor V∩U has W₂H²=0. The same is true of every smooth Zariski open subset of V∩U, since its lowest-weight cohomology is obtained by restriction from a smooth proper compactification dominating one of V∩U. If a weight-four class on a smooth open subset of U were killed by removing the restricted polar, strictness and Gysin would produce a class in this zero weight-two space. Thus adjoining the polar to any already deleted boundary preserves every weight-four class on that open subset. The same statement holds for each of the other two original Y-polars by cyclic symmetry, and hence for all three jointly.

On the normalized single-holomorphic-form chart, F_Y differs from the original Y₂-polar by an invertible coordinate monomial. Indeed y=Y₂ on c=1 and the other chart variables depend only on a,b,d,q. The resulting exclusion applies to the coordinate divisors, critical cone and three Y-polars together. Additional singular or nontransverse divisors can still occur in earlier chart currents and in rational primitive candidates. This is a support exclusion for the original nonzero primitive weight-four class.

References: [Hamm and Lê, Theorem 1.1.3 and Section 1.4](https://www.numdam.org/article/BSMF_1985__113__123_0.pdf), [Hausen, Mauz and Wrobel, Theorem 3.9 on toric nondegenerate complete intersections](https://doi.org/10.1007/s00229-022-01400-3).
