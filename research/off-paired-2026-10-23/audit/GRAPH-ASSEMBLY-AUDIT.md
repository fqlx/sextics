# Independent six-support graph assembly audit

The six denominators, exact source-addition formulation, target binding,
gauges and sampled saved columns are correct. The reported modular solve
found no candidate. This audit did not rerun the large solver or establish
characteristic-zero inconsistency. No certificate has been found.

The audited constructor is `graph-assembly/build_assembly.py`, with saved
`assembly-XY-1000003.bin/json`. The live target remains at commit
`21fccb6b4f1d4070ddaa30195a78f268247569e6`. Exact AST/Fraction comparison
confirms the metadata's immutable \(F,A\) and current \(q=1\).

## All six supports use the same physical cubic

Write \(F=H_X+F_Y+M\), with its entire actual mixed polynomial \(M\).
For either block, choose two coordinates, let \(T\) be the sum of their
sixth powers and \(K\) the product, and define

\[
D=F_YT^2+16H_XK.
\]

There are three held-out choices from the X block and three from the Y
block. The same asymmetry in \(H_X,F_Y\) is intentional: both use the
same normalized cubic parameter \(\kappa=M^3/(H_X^2F_Y)\). The Y supports
are not defined by interchanging those two coefficient functions.

The independent exact universal identity is

\[
\begin{aligned}
D_{54}&=16KT^4M^3-H_X^2F_Y(T^2-16K)^3,\\
Q_{36}&=16KF_Y^2T^2+48KH_XF_YT^2
        -256K^2H_XF_Y+H_X^2T^4,\\
D_{54}+DQ_{36}
 &=16KT^4F\bigl(M^2-M(H_X+F_Y)+(H_X+F_Y)^2\bigr).
\end{aligned}
\]

It holds for arbitrary \(T,K\), so applies to all six angle supports.
On the finite normalized Fermat angle, \(q^6=K/T^2\), and its fixed
elliptic cubic coordinate satisfies
\(j^3=(1-16q^6)^3/(16q^6)\). Equating this to the actual \(\kappa\)
gives exactly \(D_{54}\). No coupling term or source character is removed.
This validates the support construction, without claiming a source Gysin
class on its components.

Each \(D_i\) is homogeneous of degree eighteen and coprime to \(F\) over
\(\mathbb C\). There are short independent resultant witnesses for all
six. Set all X coordinates to one and all but one Y coordinate to zero,
leaving that coordinate \(y\) free. For an X support, choose \(Y_0\):

\[
F=y^6+3,\quad D_i=4y^6+48,\quad D_i\bmod F=36.
\]

For a Y support, choose a Y coordinate among its selected pair:

\[
F=y^6+3,\quad D_i=y^{18},\quad D_i\bmod F=-27.
\]

The resultants are respectively \(36^6\) and \((-27)^6\), both nonzero.
Since \(F\) is monic in the chosen \(y^6\), an independent-of-\(y\)
common factor is also impossible. Thus all six, and their product, meet
the complex denominator coprimality requirement.

## Exact addition of physical sources

For each support, the matrix imposes

\[
L_{D_i}(N_i)+A_iD_i^2=0\pmod{F^2},\qquad
L_D(N)=-DN(F)+F(D\operatorname{div}N-N(D)),
\]

and separately imposes \(\sum_i A_i=A\). The local source columns have
positive \(A_iD_i^2\) coefficients and positive source-sum entries. The
sole nonzero right-side source-sum row is the actual monomial
\(X_0^3Y_0^3\) with coefficient one. There is no sign reversal between
the local equations and the source-addition rows.

This is a valid constructive assembly. If exact polynomials satisfy

\[
A_iD_i^2+L_{D_i}(N_i)=F^2Q_i,\qquad \sum_iA_i=A,
\]

then define

\[
D=\prod_iD_i,\quad
N=\sum_iN_i(D/D_i),\quad Q=\sum_iQ_i(D/D_i)^2.
\]

Exact rational-current addition gives the full original identity

\[
AD^2-DN(F)+F(D\operatorname{div}N-N(D))=F^2Q.
\]

In particular, \(L_{D_1D_2}(N_1D_2)=D_2^2L_{D_1}(N_1)\) as an exact
polynomial identity; the cross derivative terms cancel. Three independent
exact polynomial checks across X/X, X/Y and Y/Y supports confirmed this
formula. The six-support product has degree 108, combined numerators
have degree 109 and its quotient has degree 210.

This is a sufficient sum of currents with individual denominators. It is
not a classification of every current whose denominator is the product:
in several variables a general mixed-denominator fraction need not split
into these six polynomial-numerator fractions.

## Complete source and numerator spaces

The group weights and exact gauges are the same as in
`GRAPH-D18-AUDIT.md`. Every \(D_i\) has character zero, and averaging
preserves the identity and source-sum equation. All degree-six source
monomials of target character \((3,0)\) are included; there are exactly
twenty-four. Sources outside that character need not be retained because
the same character projection can be applied to the entire assembly.

For each support, the complete projected degree-nineteen numerator space
after the exact \(N_i\bmod F\) and radial gauges has 5,291 monomials.
The independent enumeration matches all saved names in order. Each support
adds its twenty-four source columns, for a total of 31,890 columns.

The quotient gauge preserves the local source because
\(L_{D_i}(FM)=F^2(D_i\operatorname{div}M-M(D_i))\). The radial gauge is
an exact kernel for any degree-eighteen denominator. Thus neither loses
sources or numerator solutions. All local rows have degree forty-two,
character \((3,0)\), and \(Y_0\)-degree below twelve after exact monic
\(F^2\) division. The distinct source-sum rows are exactly the twenty-four
source indices and cannot collide with a local support row.

## Independent saved-matrix audit and limited solve status

`verify_graph_assembly_fraction.py` independently checked the exact target,
all six denominators and complex coprimality witnesses, the universal graph
factorization, every source/numerator name and all row gradings. It parsed
all 144 source columns and verified their single correct source-addition
entry and absence of entries in another local block.

It also reconstructed twenty-four complete columns with sparse exact
Fraction arithmetic and independent \(F^2\) long division, including two
source columns and two numerator columns for each of the six supports.
Every coefficient matched the saved modular matrix. The entire right side
was independently checked. The matrix has 149,940 rows, 31,890 columns
and 7,486,019 nonzero matrix entries. No large elimination was rerun.

Audited hashes are recorded in `graph-assembly-fraction-results.json`:

```
build_assembly.py
3d36e50df88939a8532a970eb67aff6010125ee87a7893504728e39cfdf0f892
assembly-XY-1000003.json
72edfbafbb3d24d072b010447787b8d5bb4074b1d5de522f67c9c1cd85190215
assembly-XY-1000003.bin
84a80b2d5c18c9c3bce4cbe296caaf11c12ea5efdc06f9d0758198c05f1ecbc9
```

The saved X-only solve reports modular inconsistency at prime 1000003
with rank 15,724. The saved six-support solve also reports modular
inconsistency at that prime, with rank 31,466 and an augmented contradiction.
Those are the constructor's solver reports, not ranks independently
recomputed here. They give no candidate from this assembly at that prime;
they do not establish characteristic-zero impossibility or exclude other
source-carrying currents on these graph supports.
