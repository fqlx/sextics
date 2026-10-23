# Cyclic-triple-residual: literal Fermat-cone support

The fixed reduced support

`D = X2^6 + Y0^6 + Y1^6 + Y2^6`

cannot serve the actual source `A=X0^3 Y0^3`, `q=1`, for the exact pinned polynomial in `instance.rec`. This is a characteristic-zero conclusion established by a modular rank and an exact rank upper bound. It does not exclude other supports or solve the target.

## Complete linear system

For this degree-six denominator, normalized certificates are equivalent to

```
Σ_i Ni Fi = A D,
D div(N) − Σ_i Ni Di = F Q,
```

with all `Ni` homogeneous of degree seven and `Q` homogeneous of degree six. The quotient is unrestricted; a strict certificate was not imposed. The normalization and prescribed-support theorem are in `sextics/docs/01-certificates.md`.

Both `F` and `D` are invariant under `X2 -> ζ3 X2` and the simultaneous sign change of all three Y variables. The source has μ3 character zero and Y parity odd. Projecting the polynomial identities onto this character gives the entire required block without losing a solution. For `Ni`, the X2 exponent is congruent to one modulo three if `i=X2`, and zero otherwise; its Y parity is odd for X components and even for Y components. For `Q`, the X2 exponent is zero modulo three and Y parity is odd. No other symmetry is imposed.

The resulting system has 1,129 numerator columns, 119 quotient columns, and 2,760 coefficient rows. `search.py` multiplies both equations by seven, so its matrix and right-hand side are integral.

## Exact upper bound and modular lower bounds

For any linear vector field `V`, set

```
N = F V − V(F) Z/6,
Q = D div(V) − V(D),
```

where `Z` is the Euler vector field. Euler's identities give

```
N(F)=0,
D div(N)−N(D)=F Q.
```

The required character contains exactly twelve mixed linear fields: `Yj ∂Xi` for `i=0,1`, and `Xi ∂Yj` for `i=0,1`, `j=0,1,2`. The script constructs all twelve coefficient vectors after multiplying by 42, checks their matrix products are literally zero over the integers, and finds their rank to be twelve modulo 1,000,003. Hence the rational matrix rank is at most `1248−12=1236`.

At that prime the coefficient matrix rank is exactly 1,236, while the augmented matrix rank is 1,237. Reduction cannot increase the rational rank. Consequently the rational coefficient rank is exactly 1,236 and the right-hand side is outside its span, also after extension to C.

Thus no normalized fixed-D certificate exists. Since D is reduced and legal, the prescribed-support theorem further excludes arbitrary pole multiplicities with this same support. A union with new reduced components is a different support and is not excluded here.

## Reproduction and provenance

Run:

```
python /workspace/research/round10/fermat_cone_fixed/search.py
```

`result.json` binds the complete `instance.rec` SHA256, polynomial, source, support, dimensions, ranks, and exact kernel checks. `packet.pickle` stores all integer sparse columns, the right-hand side, monomial labels, and the twelve exact kernel vectors. No repository file was modified and nothing was posted externally.
