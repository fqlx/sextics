# One graph denominator for the exact off-paired target

This packet investigates one geometrically motivated denominator, not a degree
bound or a denominator-power search. The complete reduced system is inconsistent
at both tested primes. No certificate has been produced.

The immutable source is

\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)
+\tfrac12X_0^3X_1Y_0Y_1+\tfrac12X_1^3X_2Y_1Y_2
+\tfrac13X_0^2X_1X_2Y_0Y_2,\quad A=X_0^3Y_0^3,\quad q=1.
\]

Write \(H_X=\sum X_i^6\), \(F_Y=\sum Y_i^6\),
\(T=X_1^6+X_2^6\), \(K=X_1^6X_2^6\). The single tested denominator is

\[D=F_YT^2+16H_XK,\qquad \deg D=18.\]

Its origin is the physical factorization in
`../scaling/cm-companion/full-coupling-graph.py`. That graph construction alone
does not establish a source primitive.

## Complete linear reduction for this denominator

Let

\[L_D(N)=-D\sum_iN_iF_i+F(D\,\mathrm{div}N-N(D)).\]

The requested identity is \(L_D(N)=-AD^2\pmod {F^2}\), with
\(\deg N_i=19\). The following are exact polynomial identities:

\[
L_D(FM)=F^2(D\,\mathrm{div}M-M(D)),\qquad L_D(Hz)=0
\]

for \(\deg M_i=13\), \(\deg H=18\), and
\(z=(X_0,X_1,X_2,Y_0,Y_1,Y_2)\). The second follows from Euler's identities
for \(F,D,H\), of degrees \(6,18,18\).

Since \(F\) is monic in \(Y_0^6\), reduce each numerator modulo \(F\)
to exponents \(e_{Y_0}<6\). Use the radial identity to remove every monomial
of \(N_{Y_0}\) divisible by \(Y_0\): subtracting \(Hz\) changes other
numerators only by terms with \(e_{Y_0}\le4\). Thus the gauge retains all
solutions, rather than imposing an additional ansatz. Finally reduce the
entire identity modulo the monic polynomial \(F^2\), eliminating all quotient
unknowns and retaining only rows with \(e_{Y_0}<12\).

The diagonal character projection from the original packet is exact in
characteristic zero: \(F,D\) have character zero and \(A\) has character
\((3,0)\) under the displayed \(G_{36}\) weights. Averaging an arbitrary
solution yields one in these projected spaces.

`build_system.py` imports the original exact target and produces the reduced
matrix over a supplied prime. At \(p=1000003\), the result has 20,085 rows,
5,291 numerator columns, and 549,582 nonzero matrix entries. It also saves the
target binding, names of numerator monomials, and every retained row exponent.

An independent sparse `Fraction` audit checked twelve randomly chosen
numerator columns and the full right side against the original definition of
\(L_D\), including exact polynomial division by \(F^2\). It also checked
degree 42, row character \((3,0)\), denominator degree 18, and denominator
character zero. The audited columns matched the saved modular matrix.

A failed modular consistency test is only feedback for this single denominator
at that prime; it is not a characteristic-zero nonexistence proof and says
nothing about unrestricted denominators.

## Results and reproduction

| Prime | Coefficient rank | Augmented rank | Rows | Numerator columns |
| --- | ---: | ---: | ---: | ---: |
| 1000003 | 5220 | 5221 | 20085 | 5291 |
| 1009 | 5220 | 5221 | 20085 | 5291 |

Both runs finished in under one second using approximately 14 MB peak RSS.
`results.json` binds source hashes, exact denominator, scope, checks, and results.
`solve_sparse.cpp` is a bounded single-threaded sparse row Gaussian solver with
low Markowitz-score pivot selection and solution extraction for consistent
systems. `selftest_solver.py` checks it against independent dense modular
elimination on eight systems, including dependent-column systems; consistent
solutions are substituted into every original equation.

Run from this directory:

```sh
g++ -O3 -std=c++17 -DNDEBUG solve_sparse.cpp -o solve_sparse
python3 selftest_solver.py
python3 build_system.py --prime 1000003
python3 audit_system.py 1000003
./solve_sparse system-1000003.bin solve-1000003.json 60 1000
python3 build_system.py --prime 1009
python3 audit_system.py 1009
./solve_sparse system-1009.bin solve-1009.json 60 1000
```

No exact rational solution, exact characteristic-zero rank, or exact dual
obstruction has been reconstructed. In particular the graph's geometric
splitting still has no source primitive established by this calculation.
