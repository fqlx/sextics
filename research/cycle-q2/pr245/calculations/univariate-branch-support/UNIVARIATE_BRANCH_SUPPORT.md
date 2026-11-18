# The full univariate branch discriminant and its two coefficients

With q=Y₁ and Q=q⁶ as in CURVE_POLAR_SUPPORT.md write the original equation as F=q⁶+c₁q+f. Here c₁q=m+n. On the coordinate torus all variables are nonzero.

For the projection forgetting q, the condition for a multiple root is Δ=6⁶f⁵−5⁵c₁⁶=0. On X and at a point of Δ=0, c₁ cannot be zero, since that would also give f=q=0. Thus its pullback is the union of the hypersurfaces

    P_k=kQ+c₁q=0,     6⁶(k−1)⁵=5⁵k⁶.

This follows by substituting f=−q⁶−c₁q and k=−c₁/q⁵. Explicitly c₁=−kq⁵ and f=(k−1)q⁶ so Δ=q³⁰[6⁶(k−1)⁵−5⁵k⁶]. The coefficient polynomial has one double root k=6 and four other distinct roots. Neither k=0 nor k=1 occurs. Setting s=6(k−1)/(5k) gives s⁵=k/6 and s⁶=(k−1)/5. Consequently

    F(sq)=F(q)−[(6−k)/(5k)]P_k,     6(sq)⁶+c₁sq=sP_k.

Scaling q by s with the other homogeneous coordinates fixed identifies {P_k=F=0} with the ordinary ramification component {6Q+c₁q=F=0} inside the torus. The inverse scales by 1/s. The first identity establishes equality of the defining ideals after substitution and the second identifies the two polar equations. In particular all components are smooth and all have W₂H²=0 by the polar proof. This is a statement about the full pullback of the discriminant, including all four simple-root components.

The loci c₁=0 and f=0 on X also have smooth torus intersections and zero W₂H². For c₁=0 take the ambient binomial m+n=0, a connected torus since the character m/n is primitive. Its initial equations are binomials or monomials. For a binomial face with q of minimum weight, q∂qF₀=6Q at each common zero because both couplings m,n are simultaneously present or absent. The derivative q∂q(m+n) vanishes, which ensures transversality. For higher q weights the case analysis is identical to the last two bullets of CURVE_POLAR_SUPPORT.md, including the same nonzero exceptional-face resultant. Degree-six Veronese weak Lefschetz and transverse deformation therefore identify the H² of its section with the pure weight-four H² of the ambient torus.

For f=0 the relation F=0 is equivalent to P₁=Q+m+n=0 on the torus. The ambient {P₁=0} is a punctured-line product as before. If q does not have least weight, the arguments for {6Q+m+n=0} are unchanged; at a zero of a face containing Q its log q derivative is now 5Q. If q has least weight, P₁₀ contains Q and exactly the surviving m,n terms of F₀. Its log q derivative is 5Q at a common zero. The difference F₀−P₁₀ is independent of q and is nonzero whenever there is a common zero: if q alone were minimal, P₁₀ would be a monomial. This difference is the restriction of F to q=0 and all other coordinates outside the minimum set zero. Its gradient cannot vanish at torus zeroes by the same degree-16 Macaulay test for the Euler equations of F (with m=n=0). Thus the two initial forms are transverse on every face. The weak Lefschetz argument again gives W₂H²=0.

Strictness of the Gysin map for weights and the lowest-weight property of smooth compactifications now permit deleting all these divisors, for each of the three original Y variables, in any order. This preserves all weight-four classes on an initial smooth open subset. Taking that initial open to be U minus the critical cone gives the joint support exclusion for coordinates, that cone, all three Y-coefficient pairs, and all three univariate branch discriminants. The argument does not apply to arbitrary base divisors of the elliptic or genus-ten moduli map.

See the preceding CURVE_POLAR_SUPPORT.md replay for the exceptional resultant, finite-field rank and topological comparison.
