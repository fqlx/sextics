# Strict growth of a proper Higgs subspace at Fermat

Use the source and tangent monomial tuples recorded by
`CycleQ2FermatHiggs`, in their native order. There are 33 source monomials
uᵢ and 35 tangent monomials tₘ. The lower basis can be indexed by the
monomials s−uⱼ, where s=(4,4,4,4,1). Multiplication by tₘ in the Fermat
Jacobian sends uᵢ to s−uⱼ if uᵢ+uⱼ+tₘ=s and to zero otherwise.

Order the upper and lower monomials by increasing lexicographic exponent
in their **own** exponent vectors, so the lower order on the dual *indices*
is reversed. For any subspace W in one of the two graded spaces, let P(W)
be its possible leading nonzero monomial indices. Row elimination gives
|P(W)|=dim W. If i∈P(W) and multiplication by tₘ sends uᵢ to s−uⱼ,
then the leading term of tₘ·w is s−uⱼ for any w of leading index i.
All surviving smaller terms remain smaller because their exponents are
translated by the same tₘ. Consequently any W′ containing every tₘ·W
has P(W′) containing every neighbor of P(W).

The graph is symmetric and contains the following odd cycle through every
vertex exactly once (indices start at zero):

    0 10 21 1 6 31 8 14 27 19 2 32 4 18 12 29 3
    26 11 30 5 28 7 16 15 9 13 22 20 17 23 24 25

Each successor and each predecessor lies in the neighbor set. For any
nonempty proper S the union of its successor and predecessor translates
has cardinality strictly bigger than |S|. Equality would force the two
translates to coincide and S to be stable under the two-step translation,
which is transitive since the cycle has odd length. Thus dim W′ > dim W
whenever 0 < dim W < 33. The certificate `hall_cycle.py` recomputes
all 389 directed edges, compares the full 35×33 complement table to the
native Lean source provided as an argument, and verifies the cycle.

For each fixed r between 1 and 32, existence of a stable pair of r-planes
is a closed condition on the matrix tuple. The incidence equations are
vanishing of the composites from the upper tautological bundle to each
lower quotient, and projection from the product of Grassmannians is proper.
The complement of the union of the 32 images is an open containing the
Fermat tuple. Hence the strict obstruction to equal positive proper ranks
also holds on an open in the algebraically varying Jacobian family.

The argument applies to pairs of graded subspaces with DₘW⊆W′ for every m
and dim W=dim W′, for example from a pure rational weight-three subvariation
with only types (2,1),(1,2) once the actual geometric Higgs comparison has
been supplied. It does not establish the comparison or the existence of
a given nonzero proper Gysin family.
