# Independent audit of the direct fixed-D18 certificate system

The fixed denominator, target binding, polynomial gauges, character projection
and sampled matrix columns are correct. The large linear solve was not rerun.
No candidate is asserted and no certificate has been found.

Audited files are
`/workspace/off-paired-research-new/graph-denominator/build_system.py` and its
`system-1000003.bin/json`, against the live immutable target at repository
commit `21fccb6b4f1d4070ddaa30195a78f268247569e6`. This audit writes only this
note and changes none of those files.

## Exact target and denominator

Independent AST/Fraction polynomial parsing confirms that the metadata's
\(F,A\) equal the current exact target in order
\((X_0,X_1,X_2,Y_0,Y_1,Y_2)\), and the current record has \(q=1\).
The imported packet target is therefore being used for the correct source;
no presentation hash is being used as a substitute for polynomial equality.

The denominator is exactly

\[
D=F_Y(X_1^6+X_2^6)^2
 +16(X_0^6+X_1^6+X_2^6)X_1^6X_2^6,
\quad F_Y=Y_0^6+Y_1^6+Y_2^6.
\]

It is a nonzero homogeneous polynomial of degree eighteen. It is also
coprime to \(F\) over \(\mathbb C\), independently of any irreducibility
assumption about \(F\). Regard both as polynomials in \(y=Y_0\). The
specialization \(X_0=X_1=X_2=1,Y_1=Y_2=0\) gives

\[
F=y^6+3,\qquad D=4y^6+48,\qquad D-4F=36.
\]

Consequently the \(y\)-resultant specializes to \(36^6\ne0\), so it is
not identically zero. There is no common factor of positive \(y\)-degree.
There is no common factor independent of \(y\) either, since \(F\) is
monic in \(y^6\). Thus this exact fixed denominator passes the required
complex coprimality condition.

## Gauge preservation and the full original identity

For a polynomial vector \(N\), define

\[
L_D(N)=-D\,N(F)+F(D\operatorname{div}N-N(D)).
\]

The original certificate condition is precisely

\[
AD^2+L_D(N)=F^2Q.
\]

Here \(\deg N_i=19\), both sides have degree forty-two, and the exact
quotient has degree thirty. The saved matrix's right side is correctly
\(-AD^2\) modulo \(F^2\).

For every vector \(M\), direct product differentiation gives

\[
L_D(FM)=F^2(D\operatorname{div}M-M(D)).
\]

Thus replacing each \(N_i\) by its remainder modulo the monic polynomial
\(F\) preserves the certificate condition modulo \(F^2\). The quotients
\(M_i\) are homogeneous of degree thirteen. This is an exact gauge, not
an extra restriction on the unknown numerators.

For \(z=(X_0,X_1,X_2,Y_0,Y_1,Y_2)\) and any homogeneous \(h\) of degree
eighteen, Euler's identities give

\[
N=hz:\quad N(F)=6hF,\quad
\operatorname{div}N=24h,\quad N(D)=18hD,
\qquad L_D(hz)=0.
\]

After the first gauge, all \(Y_0\) exponents are below six. Divide the
part of \(N_{Y_0}\) divisible by \(Y_0\) by \(Y_0\), obtaining such an
\(h\) whose \(Y_0\)-degree is at most four, and subtract \(hz\). This
removes exactly those \(N_{Y_0}\) monomials. All other components retain
\(Y_0\)-degree at most five. Hence the two gauge conditions used by the
builder retain every fixed-D18 solution.

Once an exact rational or algebraic candidate is reconstructed, its gauged
numerators can be used directly. There is no need to undo either gauge.
One must calculate the exact polynomial
\(AD^2+L_D(N)\), divide it by \(F^2\), and verify zero remainder and the
full identity with that exact quotient. Modular consistency by itself does
not complete this step.

## Complete G36 projection and monic normal form

The two coordinate weight vectors are

```
(0,2,0,1,3,3), (0,0,1,0,0,5) modulo 6.
```

They define a faithful group of order thirty-six: the \(Y_0\) coordinate
detects the first generator and \(X_2\) detects the second. Every term of
\(F,D\) has character \((0,0)\), while \(A\) has character \((3,0)\).
A numerator in component \(i\) therefore needs character
\((3,0)+\operatorname{wt}(z_i)\); differentiation subtracts the same
coordinate weight in every term of \(L_D\). Averaging preserves both
gauge conditions. The \(F\) division also preserves character because its
monic \(Y_0^6\) term has character zero. The radial \(h\) has character
\((3,0)\), so that subtraction preserves all six component characters.

An independent exhaustive degree-nineteen monomial enumeration, with exactly
the two gauge restrictions and these characters, matches all 5,291 saved
column names in their saved order. No projected numerator monomial is
missing. Every saved row has total degree forty-two, character \((3,0)\),
and \(Y_0\)-exponent below twelve.

The normal form is ordinary univariate division by the monic \(F^2\) in
\(Y_0\), over the polynomial ring in the other five variables. Its leading
term is \(Y_0^{12}\), and every other term has lower \(Y_0\)-degree. The
builder's descending buckets implement this same division; each subtraction
strictly lowers the active \(Y_0\)-degree. Eliminating the quotient in this
way loses no quotient unknowns or equations.

The packed exponent representation uses six bits per coordinate. All
intermediate monomials have total degree at most forty-two, so no coordinate
reaches sixty-four and packed addition introduces no carries. Python integer
keys do not truncate. The saved binary contains row indices rather than the
packed keys, and its unsigned integer fields are within their stated range.

## Independent matrix checks

The entire binary layout was parsed and compared with metadata. Its header,
all row bounds, nonzero coefficient ranges, unique row indices per column,
matrix and right-side nonzero counts, and final file length passed. The
system has 20,085 rows, 5,291 numerator columns and 549,582 matrix nonzeros;
the right side has 159 nonzeros.

Using independent sparse `Fraction` arithmetic and exact \(F^2\) long
division, twenty columns and the complete right side were reconstructed
directly from \(L_D\), without importing the builder or its polynomial
code. They match every saved modular coefficient. The deterministic column
indices were

```
0, 397, 1050, 1051, 1413, 1887, 1921, 1979, 2070, 2071,
2317, 2888, 3045, 3046, 3264, 3265, 4315, 4316, 4745, 5290.
```

These include the first and last column of every component plus eight choices
from seed `20261022`. Six additional exact polynomial checks confirmed the
\(FM\) gauge, one in every component, and an independent degree-eighteen
monomial confirmed the radial identity. None of these checks runs the large
linear solver.

Audited SHA-256 values:

```
build_system.py
95fd63dde2971b522d987df0707d978967f53e219d6f4429142fc1c8355b563b
system-1000003.bin
0d5353cf29d9c3392e127edecee691cb76737ed1adf269aa2a6358a84aa7d2df
system-1000003.json
51cb6fa5a98639346c4c85ade193b94f5fc13f3630ce381ea40b0f175a551fbd
```

This validates the constructive system and its exact gauges. It asserts no
large-solver result, characteristic-zero consistency, or source primitive.
