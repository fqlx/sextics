# The actual normalization of the proposed C=0 support

This checks one proposed constructive support; it is not a certificate for the
off-paired target. All variables below are projective base coordinates
`(t,x,y,z)=(X0,X1,Y0,Y1)`. Put

\[
 H=t^6+x^6+y^6+z^6+\tfrac12t^3xyz,
 \qquad C=x(\tfrac12x^2z+\tfrac13t^2y).
\]

The divisor `C=0` has a plane component and the nonnormal cubic component
`S: t²y+(3/2)x²z=0`. In particular, the latter is not a quadric, and applying
smooth cyclic-cover vanishing directly to this singular surface would not be
valid.

## Normalization and the branch curve

The normalization of `S` is the Hirzebruch surface
`F1=P(O(1) ⊕ O(2))`. Its finite birational map is

\[
 [t:x:y:z]=[r_0k:r_1k:-\tfrac32r_1^2l:r_0^2l].
\]

The pullback of a hyperplane is the ample tautological divisor
`L=C0+2f`, with `L²=3`. The section `k=0` maps two to one onto the singular
line `t=x=0`; there is no contracted curve. The restriction of `H` is

\[
 (r_0^6+r_1^6)k^6+
 (r_0^{12}+\tfrac{729}{64}r_1^{12})l^6
 -\tfrac34 r_0^5r_1^3k^4l^2.
\]

Its zero divisor on `F1` is smooth. On the interior chart `r0=k=1`, write
`r=r1`, `s=l` and

\[
 A=1+r^6,\quad B=1+\tfrac{729}{64}r^{12},\qquad
 h=A+Bs^6-\tfrac34r^3s^2.
\]

If `h=h_s=0` and `r s != 0`, then

\[
 s^2=\frac{2A}{r^3},\qquad
 P(r):=16BA^2-r^9=0.
\]

On this locus `P'(r)=32 B A h_r`, so an interior singularity would be a
multiple root of `P`. With `u=r³`, four times `P` is

\[
 p(u)=(64+729u^4)(1+u^2)^2-4u^3.
\]

Exact rational polynomial arithmetic gives `gcd(p,p')=1`, and `p(0)=64`.
Thus there are no interior singularities. On `l=0` the branch meets the six
simple roots of `r0^6+r1^6`, and on `k=0` it meets the twelve simple roots of
`r0^12+(729/64)r1^12`. The remaining fibres `r0 r1=0` have a nonzero fibre
derivative at every branch point. These checks cover `F1`.

## Sixth-root cover and differential forms

Let `T` be the degree-six cover defined by `q^6=H|F1`, where `q` is a section
of `L`. The smooth branch result makes `T` smooth. For its finite projection
`pi`,

\[
 \pi_*\mathcal O_T=\bigoplus_{j=0}^{5}\mathcal O_{F1}(-jL).
\]

For `j>0`, Serre duality and Kodaira vanishing for the ample line bundle `jL`
give `H¹(F1,O(-jL))=0`. The rational surface `F1` also has `H¹(O)=0`.
Consequently `q(T)=0`. Moreover
`H^{2,0}(T)^{mu6}=H^{2,0}(F1)=0`.

The part of the original fourfold above this component of `C=0` has a normal
birational model given by a finite diagonal quotient of

\[
 T\times E_F,\qquad E_F:\ A^6+B^6+Q^6=0,
\]

with the diagonal sixth-root action. Here `E_F` is the genus-ten Fermat
curve; its elliptic `j=0` factors do not change the following calculation.
Kunneth decomposes holomorphic two-forms on the product as

\[
 H^{2,0}(T)\otimes H^{0,0}(E_F)
 \;\oplus\;
 H^{1,0}(T)\otimes H^{1,0}(E_F).
\]

The second summand vanishes and the invariant part of the first vanishes.
Finite quotient singularities and their resolution do not create
holomorphic two-forms. Hence this normal support has `h^{2,0}=0`.

The other component `x=0` reduces to the smooth plane branch
`H=t^6+y^6+z^6`; its sixth-root surface is likewise smooth with irregularity
zero. The same product calculation gives no holomorphic two-form there.

This rules out the proposed `C=0` support as a source of a holomorphic
two-form whose Gysin image could equal the nonzero `(3,1)` target. It does
not rule out supports with different equations, a deformation of this
support, or a current with other pole divisors. In particular, it is not a
bounded denominator search and supplies no rational primitive.

The companion script `verify_c0_normalization.py` checks the substitution,
interior singularity eliminant, and squarefreeness over the rationals.
