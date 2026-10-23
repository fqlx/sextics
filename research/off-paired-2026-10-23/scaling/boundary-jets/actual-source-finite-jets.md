# Explicit finite reduction of the actual boundary-source jets

This constructs compatible identities for the actual source and its
parameter jets. It does not construct a scalar companion primitive or
close the physical current equation.

Let `Y=(Y0,Y1,Y2)`, `C=sum Yi^6` and

\[
 B=b_{01}Y_0Y_1+b_{12}Y_1Y_2+b_{02}Y_0Y_2,
 \qquad G=C+\lambda B^3.
\]

The coefficients `b_ij` retain their exact dependence on `X`. In the
three-normal construction `lambda=1/(27(ST)^3)`. The actual plane source
has the homogeneous degree-nine numerator

\[
 \gamma=\frac{Y_0^3(C-2\lambda B^3)\Omega_Y}{G^2}.
\]

Its scalar first jets, with `Y` fixed, are

\[
 \partial_\lambda\gamma=
 -\frac{4Y_0^3B^3\Omega_Y}{G^2}
 +\frac{6\lambda Y_0^3B^6\Omega_Y}{G^3},
\]

\[
 \partial_X\gamma=
 -\frac{12\lambda Y_0^3B^2B_X\Omega_Y}{G^2}
 +\frac{18\lambda^2Y_0^3B^5B_X\Omega_Y}{G^3}
\]

when `lambda` is held fixed. General physical derivatives follow by the
chain rule; `B_X` is a quadratic combination of the three displayed
cross monomials. Thus only the four degree-fifteen numerators
`Y0³ B⁶` and `Y0³ B⁵ {Y0Y1,Y1Y2,Y0Y2}` need pole-three reduction for
these first jets.

## A rational reduction operator with a proved denominator

For a degree-`m` polynomial `P`, use fixed Fermat division

\[
 P=P_{\rm std}+\sum_i A_iY_i^5:
\]

assign each nonstandard monomial to the first index with exponent at
least five. Define the explicit linear operator

\[
 M_m(P)=P+\frac\lambda2B^2\sum_iA_iB_i.
\]

Then the exact polynomial identity is

\[
 M_m(P)=P_{\rm std}+\frac16\sum_iA_iG_i.
\]

On the finite monomial space, `M_m` is the identity at `lambda=0`.
Therefore its determinant is a nonzero rational polynomial, and its
inverse is explicitly its adjugate divided by that determinant. This
does not rely on an unverified generic rank computation.

At degree fifteen the space has dimension 136 and there are no standard
monomials. For an actual target `P15`, let
`Q15=M15^-1(P15)` and let `A15` be its Fermat-division coefficients.
Then `P15=sum A15_i G_i/6` exactly. Griffiths' rational form identity
gives

\[
 \frac{P_{15}\Omega_Y}{G^3}=
 \frac{\operatorname{div}A_{15}\,\Omega_Y}{12G^2}
 -d_Y\left(\frac{\iota_{A_{15}}\Omega_Y}{12G^2}\right).
\]

At degree nine the space has dimension 55, with exactly ten standard
monomials (`all exponents <=4`). Given `P9`, form `Q9=M9^-1(P9)` and
its division `Q9=Q9_std+sum A9_i Yi^5`. Then

\[
 \frac{P_9\Omega_Y}{G^2}=
 \frac{Q_{9,\rm std}\Omega_Y}{G^2}
 +\frac{\operatorname{div}A_9\,\Omega_Y}{6G}
 -d_Y\left(\frac{\iota_{A_9}\Omega_Y}{6G}\right).
\]

The degree-three numerator of the pole-one term has ten monomials.
These identities give twenty fixed representatives plus explicit
rational one-form corrections for every actual first jet. They also
define the finite module for higher jets by repeated reduction. No
large unrelated connection is needed to state or verify the identities.

Every coefficient derivative is compatible with the construction. For
example, if `Q=M^-1 P`, then

\[
 \partial_XQ=M^{-1}(\partial_XP-(\partial_XM)Q).
\]

Thus all `X` and `B` derivatives are retained as rational identities,
including derivatives of the denominator determinants.

## The physical d/e logarithmic boundary is retained

The second Fano companion has
`J=G-d³-e³`. The physical curve source is the ordered normal residue in
`(J,d,e)` of `P9 Omega_Y dd de/(J² d e)`. The factor `1/(d e)` is not
discarded or treated as polynomial density.

The gradient relations above remain exact because `J_i=G_i` for the
three `Y` derivatives. In the projective rational-form calculation,
the only Euler defect is

\[
 E_Y(J)-6J=6(d^3+e^3).
\]

Hence lifting the plane reduction to the companion produces an explicit
additional term with factor `(d³+e³)/(d e)`. Its double logarithmic
residue at `d=e=0` is zero: neither summand has the required `d^-1 e^-1`
coefficient. The other normal derivative is in a `Y` direction and does
not remove the positive `d` or `e` powers. All `lambda`, `X`, and
`b_ij` derivatives preserve this boundary vanishing. Consequently the
finite reduction identities are valid for the genuine physical
three-normal residue, with the logarithmic boundary kept explicitly.

## What remains to prove

This finite source-jet system does not assert that its twenty
representatives admit scalar companion primitives with those boundary
poles. A successful joint contraction needs the primitive for the
actual source and enough compatible derivatives, or a smaller served
cyclic submodule, together with control of homogeneous solutions and
the first elliptic parameter derivative. Rational source reduction
alone is not a substitute for that construction.

The checker verifies all 191 column identities of `M9,M15`, identity
specialization (hence the determinant argument), the four actual jet
formulas, and the exact weighted boundary Euler identity.

Prepared with OpenAI Codex assistance.
