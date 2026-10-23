# Independent audit of the complete bare-coordinate scalar equation

The equation and reconstruction in
`coupled-fresh/rank4-relative/BARE-FULL-HORIZONTAL-CLOSURE.md` are correct
for all rational currents in the compact rank-four endpoint module. The
independent standard-library verifier `verify_bare_full_fraction.py` passes
32 exact groups; results are in `bare-full-fraction-results.json`. It does
not import the primary verifier or SymPy.

## Actual source, coordinates and Piola map

Exact substitution of `a=x^3`, `C=x^3 z/2+xy/3` gives `q=xy` and the actual
endpoint H. The three stated bare derivatives of H all agree. The coordinate
Jacobian is

    det d(a,C,z)/d(x,y,z)=x^3,

so `y^3 dx dy dz=(q^3/a^2) da dC dz` with the positive displayed orientation.
There is no missing `P_a` factor.

The claimed Piola matrix was checked both by multiplying the forward
Jacobian and by checking that each cofactor column has zero divergence.
These two identities prove its divergence transformation for arbitrary
coefficient functions, not just constant vectors. The covariant connection
term transforms by the same chain rule, so the map applies to all compact
coefficient columns. Both `C_x` and `C_z` terms in the physical y-current
are necessary and present.

## Euler column and complete cyclicity

With `h=delta H`, the bare operator is `nabla_delta=nabla_C+h nabla_H`.
The previously independently verified universal cyclic H-columns give

    nabla_delta s_j=r s_(j+1)-(2+2j)h s_j/(3H),
    r=1-2Ch/(3H).

Successive bare cyclic columns `t_j` therefore have leading diagonal
`1,r,r^2,r^3` relative to `s_j`; derivative terms affect only lower cyclic
indices. Their determinant is exactly `r^6` times the established universal
determinant. No constancy of h is assumed in this argument. At the actual
point `a=1,C=1/3,z=0`, one has `H=3,N=-3,r=-1/3`, and both determinants
are nonzero. Thus the actual bare module is cyclic over its function field.

The audit also directly checks all four entries of

    N M_H e0=-2(e0+C(M_C+h M_H)e0),
    N=3H-2Ch,

against the saved original compact column matrices. This is precisely
`nabla_H omega0=-2(t0+C t1)/N`, with the correct column orientation and
sign. Constructing the actual monic `Lhat` by the stated finite matrix
recurrences and inverting this nonzero cyclic matrix is valid. The primary
note defines these rational coefficients algorithmically; it does not yet
supply an expanded coefficient table.

## Four-row reconstruction and source restoration

For a horizontal a-current `U t0`, its first two bare cyclic rows are

    (U_a-2H_a U/N, -2C H_a U/N).

Scalar cyclic reduction subtracts delta of the second row. The ordinary
product rule for delta(C)=1 cancels the standalone `-2H_a U/N`, leaving

    A_a(U)=U_a+2C delta(H_a U/N).

The z-current has the identical formula with `H_z,W`. The derivative of
`H_a U/N` or `H_z W/N` is the full actual bare derivative.

The independent verifier treats every coefficient of the companion relation
and its first three derivatives, and all four derivatives of G, as arbitrary
jets. It verifies the displayed v reconstruction in **all four rows**,
including the extra `+2C(H_a U+H_z W)/N` in `v0`. The scalar row is exactly

    -Lhat*G+U_a+W_z+2C delta[(H_a U+H_z W)/N].

The actual source and restoration signs also check in every row:

    original=F(t0+C t1), F=q^3/(3a^2 N),
    original=nabla_delta(CF t0)+[-C delta(F)]t0.

Thus `S0=-C delta(F)` and the added C-current `+CF t0` are correct. There
is no omitted derivative of N in this statement.

## Unrestricted scope and remaining work

For the bare companion, the universal cyclic reduction
`b-E_delta(b)t0=nabla_delta B_delta(b)` applies to arbitrary compact
columns. The actual bare a, C and z coordinate derivations commute, and
their pulled-back connection is flat. The discarded a- and z-column pieces
can therefore be absorbed into the C-current by adding
`nabla_a B_delta(a_column)+nabla_z B_delta(z_column)`. This proves the same
two-way completeness as the earlier scalar-closure audit. It places no
degree, pole or one-flow restriction inside the compact module.

Setting U=W=0 produces a current only in the bare C direction. After the
actual Piola map it holds original x and z fixed; this is the previously
excluded relative subproblem. The full equation retains independent U,W and
is not excluded by that result. Moving-pole and residue modules remain
additional possibilities outside this compact rank-four statement.

No rational solution `(G,U,W)` is supplied. Exact fiber Dwork corrections,
homogeneous legal denominator clearing and immutable-target verification
remain necessary for any eventual solution. No certificate has been found.
