# Boundary of the regulator form on the genus-ten curve

The generic torus curve over K=C(I,J) has equation
P=I^6 T^4 + b^9 T^2 + (I b^8/2 - J b^9)T+b^12+b^9.
Its projective Newton boundary has the following normalized valuations and tame symbols for {b,T}, with the convention (-1)^(ord b ord T)b^(ord T)/T^(ord b).

| ord b | ord T | number of points | symbol | edge equation |
|---|---|---|---|---|
| 0 | 1 | 3 | b_i, b_i^3=-1 | b^3+1=0 |
| -2 | -3 | 1 | -1 | T^2/b^3=-1 |
| -2 | -9 | 1 | -I^-6 | T^2/b^9=-I^-6 |
| 4 | 9 | 1 | -I^6 | b^9/T^4=-I^6 |

The edges have lengths 3,1,1,1; the edge roots are simple, and all places listed are K-rational. The only nonconstant boundary logarithmic differentials are opposite copies of 6dlog I. In the actual mixed top differential they wedge with dI, so their contributions vanish. In particular the bare toric defect does not obstruct the protected mixed primitive.

## Torus units on the generic curve

Extend the constants C(I) to their algebraic closure k, leaving J transcendental, and let R=k[b^±1,T^±1]. Put j=T+(1+b^3)/T+I/(2b)+I^6 T^3/b^9. All special levels j=j0 over k are irreducible. Indeed b^9 T(j-j0) is the quartic P with J=j0. Its coefficient valuation at b=0 has lower Newton edge joining (0,9) and (4,0). The coefficient of T has valuation 8, and the coefficient of T^2 has valuation 9. Thus every root has valuation 9/4. Every irreducible factor over k(b) has degree divisible by 4, by the valuation of its constant term divided by its leading coefficient. The quartic is primitive with constant leading coefficient I^6 in k[b]. Gauss' lemma and localization at b,T give irreducibility of j-j0 in R.

The torus ring of the generic fibre is R localized at the nonzero polynomials in j. R is a UFD with units k^* b^a T^c; every polynomial in j splits over k into the primes j-j0 just found. Consequently, modulo k(j)^*, every unit on the generic torus fibre is b^a T^c. A function with divisor supported only on the last two boundary points would be such a unit. The three bottom valuations force c=0 and the (-2,-3) valuation forces a=0. Hence their difference is nontorsion in the generic Jacobian. This persists geometrically: if any multiple of a rational degree-zero divisor becomes principal over a field extension, nonzero sections of its associated degree-zero line bundle descend in dimension by base change of H^0 for the proper curve. In this case all boundary points are already rational.

It follows that a single symbol {I,f} supported on the two moving tame points cannot absorb their nonconstant opposite factors even after a nonzero multiple. This argument concerns the bare symbol. It makes no assertion about rational mixed currents with additional support, combinations of symbols with canceling interior tame divisors, or the remaining proper primitive.
