# Full matrix algebra of the Fermat Higgs directions

The 33 basis monomials and 35 tangent monomials use the zero-based order of
`CycleQ2FermatHiggs.basisMonomial` and `tangentMonomial`. Let
`T_i = higgsMatrix ℤ i`. Their entries are 1 precisely when the two basis
exponents and the tangent exponent add to the socle (4,4,4,4,1).

Set

    H = T_8 + T_17 + T_19 + T_22 + T_25 + T_27 + T_29
    J = adj(H)
    A_i = J T_i

Use the integral vector l with entries (3,-3,-1,2,1,-1,2) at
(8,16,18,23,25,29,31), respectively, and all other entries zero. Exact integer
arithmetic gives

    det H = -24
    T_4 J T_4 = l l^t.

Index 33 matrices B_a by a special index * followed by the 32 indices from
0 through 34 excluding 4, 29 and 34. Put B_* = I and B_a = A_a otherwise.
Form the 33 columns C_* = l and C_a = T_a J l otherwise. In this order,

    det C = -333002129772277037540987257626384275757114307214929177870336.

With R = A_4², symmetry of H, J and every T_i gives

    B_a R B_b = J C_a C_b^t.

Thus the coefficient matrix X=(x_ab) corresponds under their linear
combination to J C X C^t. Since J and C are nonsingular, the 1,089 matrix
words B_a R B_b form a basis of the full 33-by-33 matrix algebra over
any characteristic-zero field. Both displayed determinants are 4 modulo 7.
Checking only in that finite field already proves the corresponding word
determinant is nonzero in characteristic zero.

The same list of words determines a principal-open test on any matrix tuple.
Replace each T_i by the corresponding varying matrix, retain H, J, A_i,
B_a and R as polynomial expressions, and take the determinant of the matrix
whose columns are the vectorized B_a R B_b. At the Fermat tuple this is the
determinant of X ↦ J C X C^t. With consistent matrix-unit order it has
value (det H)^(32·33) (det C)^66. Hence its product with det H defines a
nonempty principal open. The rank-one identity above is only required at
Fermat; nonvanishing of this fixed polynomial certifies the full basis over
the entire open.

For a 33-dimensional upper space and lower space, use the perfect pairing
that identifies the lower space with the upper dual to interpret each T_i
as a map from upper to lower. If W,V are subspaces with equal dimension and
T_i(W) ⊆ V for all i, the isomorphism H identifies W with V. Consequently
H⁻¹T_i stabilizes W for all i. As J T_i = det(H) H⁻¹T_i generates the full
endomorphism algebra, W is either zero or the entire upper space. This
statement applies after arbitrary characteristic-zero scalar extension.

The application to an actual variation still needs the geometric Higgs
comparison, equal ranks of the two graded subspaces, and a nonzero geometric
subvariation. The finite calculation alone supplies none of those hypotheses.

Run `python3 verify.py --lean /path/to/data/cycle-q2/GeometricFormalInputs01Part01.lean`
to reconstruct all matrices, compare all exponents and complement positions,
and verify both determinants and the rank-one identity. The script uses only
the Python standard library.

Prepared for fqlx with OpenAI ChatGPT assistance.
