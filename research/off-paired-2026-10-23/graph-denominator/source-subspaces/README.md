# Sources served by the six fixed CM graph supports

The existing audited `graph-assembly/assembly-XY-1000003.bin` was split into its
six homogeneous block systems, deleting exactly the 24 source-addition rows.
For each support the retained equation is

\[
L_D(N)+A_iD^2=0\pmod {F^2},
\]

where \(A_i\) has 24 degree-six target-character coordinates. This uses the
same complete numerator gauges and the same supports as the parent assembly;
no support, degree, or denominator power was changed.

At \(p=1000003\), **each of the six projected kernels has dimension two and
the same source basis**:

\[
\begin{aligned}
B_1&=\frac{X_0}{6}\frac{\partial F}{\partial Y_1}
=X_0Y_1^5+\frac{X_0X_1^3X_2Y_2+X_0^4X_1Y_0}{12},\\
B_2&=\frac{3Y_1}{2}\frac{\partial F}{\partial X_0}
=X_0X_1X_2Y_0Y_1Y_2+\frac94X_0^2X_1Y_0Y_1^2+9X_0^5Y_1.
\end{aligned}
\]

In the source order saved with each block, the nonzero entries are
\((9,1),(14,1/12),(22,1/12)\) for \(B_1\), and
\((12,1),(17,9/4),(23,9)\) for \(B_2\), using zero-based indices.
The immutable target \(A=X_0^3Y_0^3\) is source coordinate 20, hence outside
this modular subspace.

These two sources are universal: the linear polynomial vector fields
\((X_0/6)\partial_{Y_1}\) and \((3Y_1/2)\partial_{X_0}\) have zero divergence
and produce exact strict identities with \(N=Dv\), for every denominator
\(D\). They are the only linear monomial vector fields in this character.
Thus this modular calculation finds no additional source class served by the
six particular graph supports. The exact identities establish a
characteristic-zero lower bound of two; no characteristic-zero upper bound
has been proved here.

| Support | Rows | Columns | Rank | Kernel dimension | Source projection |
| --- | ---: | ---: | ---: | ---: | ---: |
| X, held 0 | 20085 | 5315 | 5242 | 73 | 2 |
| X, held 1 | 20307 | 5315 | 5243 | 72 | 2 |
| X, held 2 | 20279 | 5315 | 5237 | 78 | 2 |
| Y, held 0 | 20891 | 5315 | 5247 | 68 | 2 |
| Y, held 1 | 34173 | 5315 | 5249 | 66 | 2 |
| Y, held 2 | 34181 | 5315 | 5246 | 69 | 2 |

`extract_blocks.py` preserves the old assembly, validates each column's support,
removes only source-sum rows, and records its SHA-256. `project_sources.cpp`
copies the validated sparse solver, back-solves every free-variable nullvector,
projects to the last 24 source coordinates, and computes the reduced source
basis while retaining corresponding numerator lifts. It stores no large full
nullspace. All runs were single threaded; each took at most 2.5 seconds and
47 MB peak RSS.

`verify_projections.py` substituted all twelve saved source/numerator lifts
into every original extracted matrix row and checked zero residual. It also
matched both bases to exact derivatives of the original target polynomial.
`selftest_projection.py` independently computed dense Python RREF kernels on
six unrelated matrices and verified the entire projected basis, rank, and
dimension against the C++ program.

```sh
python3 extract_blocks.py
g++ -O3 -std=c++17 -DNDEBUG project_sources.cpp -o project_sources
python3 selftest_projection.py
./project_sources block-X0-1000003.bin block-X0-1000003.projection.json 120 1500
# Repeat the previous line for X1, X2, Y0, Y1, Y2.
python3 verify_projections.py
```

`projection-verification.json` records all ranks and checked identities;
`block-*.projection.json` contains the source bases and corresponding modular
numerator lifts. The calculation is confined to the six fixed simple-pole
graph denominators, and its dimension statements are modulo 1000003.
