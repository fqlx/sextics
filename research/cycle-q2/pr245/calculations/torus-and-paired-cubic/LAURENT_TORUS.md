# The full five-variable Laurent reduction

The proper residual is −(∇_J²ω)⊗H/12, where ω=dτ/F_y and H=(I²/6)φ₅₂+2Iφ₉₁. Put p=1/τ and regard all five variables I,p,T,y,b as invertible. The shared level equations are

    J_C=−(y⁶+1)p³−yp²/2−Iyp/2,
    J_D=I⁶T³/b⁹+(1+b³)/T+T+I/(2b),       G=J_D−J_C.

Consider the ambient form

    χ=[pI²/(6b⁵)+2pI/(bT)] dI∧dp∧dT∧dy∧db/G³.

Locally choose G and J_D as coordinates in place of p,T. Then dI∧dp∧dT=dG∧dI∧dJ_D/((J_C)_p (J_D)_T). In taking the pole-three residue at fixed J_D, both normal derivatives act on p/(J_C)_p, with factor 1/2 from the Taylor expansion. Since ω=−p dy/(J_C)_p and P_T=b⁹T(J_D)_T on D, the residual is (1/6)Res(χ) with these coordinate orders. This representation allows derivatives in all five directions.

## Exact pullback to the protected homogeneous ring

In the original sextic chart X₂=1 use the monomial map

    p=1/(X₀Y₀), b=X₁²/X₀², T=Y₀³/X₀³, I=X₁³Y₁/(X₀²Y₀²), y=Y₂.

Its matrix in the orders (I,p,T,y,b) and (X₀,X₁,Y₀,Y₁,Y₂) has determinant +12. Thus the map is a degree-12 isogeny of dense tori, and G=p³F. Converting through logarithmic volume forms gives

    pullback χ=12 N_h Ω/F³,
    N_h=X₂²(X₀⁵Y₀³Y₁²/6+2X₀²X₁⁵Y₀²Y₁).

Writing A=X₀²X₁²X₂³Y₀²Y₁²Y₂ for the protected input, there is a short homogeneous certificate.

    N_h + A/2 = (X₀²X₂²Y₀²Y₁/3) F_(X₁).

The multiplier is independent of X₁. Its Griffiths divergence is therefore zero, so the normalized class (1/6)Res(χ) pulls back to −Res(A Ω/F³). The overall sign refers to the displayed orders. The script torus_griffiths.py checks the torus determinant, all character substitutions, the homogeneous identity and the zero divergence with exact arithmetic.

## Nonvanishing on the full dense torus

All coordinate face restrictions of F are smooth wherever their projective zero sets are nonempty. Choose a nonzero coordinate of maximal absolute value M. In the derivative with respect to that coordinate, its diagonal Fermat term has absolute value 6M⁵. The remaining terms have total absolute value at most 2M⁵ for an X coordinate, or M⁵ for a Y coordinate. The same argument holds after any coordinate replacements by zero. Hence X={F=0} is smooth and its coordinate boundary is simple normal crossings.

For clarity the standard monomials of the Fermat Jacobian remain a vector-space basis in degree twelve for this particular smooth F. Divide each F_i by 6 to write x_i⁵+r_i with coefficient ℓ¹-norm at most 1/3 for r_i. For each monomial containing an exponent at least 5 choose one such i and replace x_i⁵ by −r_i. This linear replacement followed by projection onto nonstandard monomials has operator ℓ¹-norm at most 1/3. Thus one minus this operator is invertible on the finite-dimensional nonstandard subspace. It follows by linear algebra that the standard monomials span the degree-twelve Jacobian quotient. The six partials form a homogeneous regular sequence, since their common affine zero locus is the origin. The Hilbert series of their quotient is (1+t+t²+t³+t⁴)⁶, so the number of spanning standard monomials in degree twelve equals its dimension, 1751. The monomial A has every exponent at most 4 and is therefore nonzero in that quotient. The Griffiths residue isomorphism identifies its nonzero graded class with a nonzero part of the primitive middle cohomology of X. [Griffiths, On the periods of certain rational integrals](https://publications.ias.edu/node/183)

Put U=X∩(ℂ*)⁵ in the projective torus. For the simple-normal-crossing complement, the weight spectral sequence gives the image of H⁴(X) in H⁴(U) as the quotient by the sum of the Gysin images H²(D_i)(−1)→H⁴(X) for the six coordinate boundary threefolds. In detail the row of weight four at its right endpoint has d₁ given by these Gysin maps, and the spectral sequence degenerates at E₂. Each D_i is a smooth sextic hypersurface in ℙ⁴, so its H² is spanned by the hyperplane class by weak Lefschetz. Their Gysin images are all spanned by h². The primitive middle cohomology has trivial intersection with that line by Lefschetz decomposition. Consequently Res(A Ω/F³) restricts nontrivially to U. [Deligne, Théorie de Hodge II](https://www.numdam.org/articles/10.1007/BF02684692/)

This proves that the five-variable ambient Laurent form has no primitive made of Laurent coefficients with powers of G in the denominator, even allowing all five possible differential directions. Indeed an exact form would pull back to an exact form and have zero residue class on U. A rational primitive on a smaller open set is compatible with this result. Possible certificates can use divisors inside the dense torus.
