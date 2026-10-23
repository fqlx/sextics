# Fixed CM graph supports and physical-source assembly

No certificate was found. The three X-support assembly and six X/Y-support
assembly are inconsistent modulo 1000003. Projecting the six individual
homogeneous systems onto their physical source coordinates gives the same
two-dimensional subspace for every support, consisting of universal Jacobian
sources. These are modular statements about this specified construction.

The immutable target is the original off-paired \((F,q=1,A=X_0^3Y_0^3)\).
Write \(F=H_X+F_Y+M\), retaining all three mixed terms. For each of the three
coordinate pairs in either block, let \(T\) be the sum of their sixth powers,
\(K\) their product, and use

\[D_i=F_YT^2+16H_XK.\]

All six use the same normalized cubic parameter \(M^3/(H_X^2F_Y)\); the Y
supports do not interchange \(H_X\) and \(F_Y\). Their geometric origin and
complex coprimality were independently checked in
[the assembly audit](../audit/GRAPH-ASSEMBLY-AUDIT.md).

## Exact assembly interface

For every support, include all 24 degree-six sources \(A_i\) in the target
character and the complete degree-nineteen numerator space after the exact
polynomial and Euler gauges. Impose

\[
A_iD_i^2+L_{D_i}(N_i)=0\pmod {F^2},\qquad \sum_i A_i=A,
\quad L_D(N)=-DN(F)+F(D\operatorname{div}N-N(D)).
\]

If exact solutions satisfy
\(A_iD_i^2+L_{D_i}(N_i)=F^2Q_i\), their currents add by

\[
D=\prod_iD_i,\qquad N=\sum_iN_i(D/D_i),\qquad
Q=\sum_iQ_i(D/D_i)^2.
\]

These give the exact original cleared identity. The three-support result has
degrees \((\deg D,\deg N,\deg Q)=(54,55,102)\); the six-support result has
degrees \((108,109,210)\). This is a sufficient additive construction. It
does not classify every current having the product denominator: arbitrary
mixed-denominator numerators need not split into these individual currents.

| Assembly | Prime | Rows | Columns | Rank | Augmented rank |
| --- | ---: | ---: | ---: | ---: | ---: |
| Three X supports | 1000003 | 60695 | 15945 | 15724 | 15725 |
| Six X/Y supports | 1000003 | 149940 | 31890 | 31466 | 31467 |

The independent audit checked the exact target, all denominators and complex
coprimality witnesses, the universal graph factorization, complete names and
row gradings, all 144 source-addition columns, 24 full Fraction columns, the
entire right side, and the exact addition identities. It did not independently
rerun the large elimination.

## Individual sources served at the tested prime

Delete only the 24 source-sum rows from the saved six-support matrix. For each
homogeneous block, back-solve all free-variable kernel vectors and project them
onto its 24 source coordinates. Every support gives exactly the same basis
modulo 1000003:

\[
\begin{aligned}
B_1&=\frac{X_0F_{Y_1}}6
=X_0Y_1^5+\frac{X_0X_1^3X_2Y_2+X_0^4X_1Y_0}{12},\\
B_2&=\frac{3Y_1F_{X_0}}2
=X_0X_1X_2Y_0Y_1Y_2+\frac94X_0^2X_1Y_0Y_1^2+9X_0^5Y_1.
\end{aligned}
\]

These are the sources of the divergence-zero linear fields
\((X_0/6)\partial_{Y_1}\) and \((3Y_1/2)\partial_{X_0}\). With \(N=Dv\),
they satisfy exact strict identities for every denominator. They are also the
only linear monomial fields in this character. Thus the calculation supplies
no additional source class on these six ordinary simple-pole graph supports
at this prime. The target \(A=X_0^3Y_0^3\) is outside their span.

| Support | Full homogeneous rank | Kernel dimension | Source projection |
| --- | ---: | ---: | ---: |
| X, held 0 | 5242 | 73 | 2 |
| X, held 1 | 5243 | 72 | 2 |
| X, held 2 | 5237 | 78 | 2 |
| Y, held 0 | 5247 | 68 | 2 |
| Y, held 1 | 5249 | 66 | 2 |
| Y, held 2 | 5246 | 69 | 2 |

All twelve saved source/numerator lifts substituted to zero in every original
extracted row. Six independent dense Python kernel calculations checked the
projection algorithm, including rank-deficient cases. See
[the source-subspace packet](../graph-denominator/source-subspaces/README.md)
and its [verification results](../graph-denominator/source-subspaces/projection-verification.json).

These exact universal sources prove a characteristic-zero lower dimension of
two. No characteristic-zero upper dimension, exact obstruction, unrestricted
nonexistence, or denominator-power result is claimed. No powers were escalated.

`results.json` is the compact readable record and lists source, explanation,
audit, and result files. Binary matrices and executables are deliberately
excluded from its readable manifest. The saved binary computations remain
available locally for reproduction.
