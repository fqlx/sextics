# Third-kind endpoint component: a genuine constructive enlargement

This note concerns the fixed off-paired target; it is not a certificate or a nonexistence claim.

Let

\[
 Z^2=f(p)=(H+Cp)^2-4p^6,\qquad S=H+Cp,
\]

and work over a characteristic-zero field containing \(i^2=-1\). The compact genus-two basis is
\(\omega_j=p^jdp/Z\), \(j=0,1,3,4\). The omitted form

\[
 \tau=\omega_2=p^2dp/Z
\]

has simple poles at the two points at infinity. With \(u=1/p\) and
\(Z\sim\pm2ip^3\), its residues are \(\mp1/(2i)\). They are nonzero constants,
independent of \(H,C\). Consequently \(\nabla_H\tau\) and \(\nabla_C\tau\)
have zero residues and reduce to the compact rank-four space modulo rational
exact differentials. The open curve obtained by deleting the two infinities
has rank-five first de Rham cohomology. Its extra extension can contribute
compact connection terms even if the residue coefficient of the final
source is zero.

For a three-coordinate physical base \((x,y,z)\), add currents \(T_k\tau\)
to the compact currents. The residue equation is exactly

\[
 \partial_xT_x+\partial_yT_y+\partial_zT_z=0.
\]

The compact source equations retain the additional terms
\(\sum_k T_k(H_k\nabla_H\tau+C_k\nabla_C\tau)\).
Dropping these terms would discard the new construction. Every solution
must still be lifted through the rational exact differential corrections;
a modular rank hit by itself is not a primitive.

## Physical pullback and legality

On the actual endpoint curve

\[
 a^6+b^6+Cab+H=0,
 \qquad p=ab,\quad Z=b^6-a^6,
\]

one has, with \(H,C\) held fixed,

\[
 \frac{dp}{Z}=-\frac{6\,db}{6a^5+Cb},\qquad
 \tau=-\frac{6a^2b^2\,db}{6a^5+Cb}.
\]

This uses the source-current convention \(Z=b^6-a^6\). Replacing \(Z\) by its negative reverses both displayed pullback signs; the abstract curve and logarithmic identities remain valid with the chosen \(Z\). Thus the added form is rational in the actual physical endpoint variables.
Its poles at endpoint infinity are allowed rational poles. Clearing a
resulting primitive still requires the exact sextic divisibility identity,
nonzero homogeneous denominator, and complex coprimality. The expression
alone establishes none of those final certificate obligations.

## Two useful logarithmic identities

Set \(r=(S+Z)/2\). Direct differentiation gives

\[
 d\log(r/p^3)
 =\frac{dH+p\,dC}{Z}-2C\frac{dp}{Z}
                         -3H\frac{dp}{pZ}.
\]

The finite points \(P_\pm=(p,Z)=(0,\pm H)\) satisfy
\(\operatorname{div}(r/p^3)=3(P_--P_+)\). Their difference is three-torsion.
This does **not** establish torsion of the difference of the two points at
infinity, which is the extension measured by \(\tau\).

A second exact identity uses \(v=(Z+2ip^3)/S\):

\[
 \frac1{2i}d\log v
 =\frac{p^2(3H+2Cp)\,dp-p^3(dH+p\,dC)}{S Z}.
\]

At \(C=0\), its relative part becomes \(3\tau\), so the third-kind
component becomes logarithmic on that special fiber. For general \(C\),
it relates the infinity extension to the moving pair above \(p=-H/C\),
not to a zero compact derivative.

Prepared with OpenAI Codex assistance as a constructive interface audit.

## Additional connection audits

The weighted scaling has weights \((p,Z,H,C)=(2,6,6,4)\). The third-kind
form \(\tau\) has weight zero, hence

\[
 6H\nabla_H\tau+4C\nabla_C\tau=0
\]

in relative de Rham cohomology. At \(C=0\), direct differentiation yields

\[
 \nabla_H\tau=-\frac1{3H}d(p^3/Z),\qquad
 \nabla_C\tau=\frac1{3H}\omega_3-\frac1{3H}d(p^4/Z).
\]

Only the first derivative vanishes in compact cohomology on this special
fiber; the transverse \(C\)-derivative generally does not. For a
divergence-free base current \(T\), the extra compact contribution is

\[
 \left(T(C)-\frac{2C}{3H}T(H)\right)\nabla_C\tau.
\]

## A rational potential basis for the full rank-five connection

For \(j=0,\ldots,4\), the rational relative one-form

\[
 \nu_j=-\frac{p^{j+1}}{j+1}d\log r
\]

has class

\[
 v_j=\frac{3H\omega_j+2C\omega_{j+1}}{j+1}.
\]

Here \(\omega_5=(CH\omega_0+C^2\omega_1)/12\) modulo
\(-dZ/12\). Its exact derivative lifts are

\[
 \partial_H\nu_j=\omega_j-d\left(\frac{p^{j+1}}{(j+1)Z}\right),\qquad
 \partial_C\nu_j=\omega_{j+1}-d\left(\frac{p^{j+2}}{(j+1)Z}\right).
\]

Let \(A\) be the matrix with columns \(v_j\) in the basis
\((\omega_0,\ldots,\omega_4)\), and \(P\) the matrix with columns
\(\omega_{j+1}\). Then

\[
 \det A=\frac{H(729H^4-4C^6)}{360},\qquad
 M_H=(I-A_H)A^{-1},\quad M_C=(P-A_C)A^{-1}.
\]

The accompanying script `potential_rank5_connection.py` checks the determinant,
all 25 flatness entries, all 25 Euler-weight entries, and the zero residue
row. It writes the exact matrices to `potential-rank5-connection.json`.

For a current with coefficient vectors \(b_i\) in this potential basis,
the exact cohomology equation becomes

\[
 A\sum_i\partial_i b_i+
 \sum_i(H_iI+C_iP)b_i=\text{physical source}.
\]

This removes the connection matrices from the left side but does not remove
the physical coefficient or the divergence equations. Restricting all
\(b_i\) to divergence-free fields tangent to \(H\) or \(C\) merely returns
the coefficient-curve integration problem; no such restriction is justified
as a complete search.
