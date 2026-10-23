# Independent endpoint audit

Run `python3 verify_connection_fraction.py`. This uses only Python's standard
library, exact `Fraction` arithmetic, AST parsing, coefficient dictionaries, and
single-divisor polynomial division. It imports neither the primary connection
generator nor SymPy. The adjacent JSON records the exact checked data hash.

The verifier checks 75 polynomial identities: eight cleared Dwork identities,
16 Euler-matrix entries, 16 flatness entries, 16 weighted-gauge entries, the
weighted curve and discriminant, three physical endpoint identities, and four
entries of the Euler expression for the source; plus two third-kind Dwork
identities, four third-kind Euler entries and four fifth-column flatness entries.
It also checks the infinity expansion that gives constant third-kind residues.
The fixed common denominator is
\(L=4H(4C^6-729H^4)\). Matrix columns are derivatives of the corresponding basis
form, so coefficient columns carry the connection \(d+M\). In particular,
flatness uses \(\partial_HM_C-\partial_CM_H+[M_H,M_C]=0\).

The source binding parses both current and original `instance.rec` files as
exact polynomials and compares their mathematical fields to the immutable target.
Changing `q` from 1 to 2 in memory is rejected. The raw hashes differ only because
the whole record includes rendering metadata. The new canonical digest is
\(`9df3e6d7010a0ddfa608a059705b584216fa06fa8130d084d6135179370f3ccf`\).
Its JSON serialization is documented in the results; this digest is not asserted
to use the handoff's serialization.

## Source orientation

Let \(a=X_2,b=Y_2,p=ab\), with physical affine coordinate order
\((x,a,y,z,b)\). This has the same orientation as \((x,y,z,a,b)\). The source
coefficient convention must also specify which square root is called \(Z\).

For the choice \(Z=b^6-a^6\),

\[
\det\frac{\partial(F,p)}{\partial(a,b)}=-6Z,
\quad
dx\wedge dy\wedge dz\wedge da\wedge db
=\frac{dF\wedge dx\wedge dy\wedge dz\wedge dp}{6Z}.
\]

Since
\(Z^2=(F-H-Cp)^2-4p^6\), at \(F=0\) we have
\(\partial_F(1/Z)=-\partial_H(1/Z)\). The second-pole residue, with
\(dF/F\) placed first, is therefore

\[
-\frac{A}{6}\,dx\wedge dy\wedge dz\wedge\nabla_H(dp/Z).
\]

This is the handoff's sign. Choosing \(Z=a^6-b^6\) changes the sign of the
source coefficient relative to the newly named \(\omega_0\); the underlying
physical residue is unchanged. The bare curve equation \(Z^2=(H+Cp)^2-4p^6\)
does not choose this sign. This convention should remain explicit when an
eventual current is converted to the physical certificate.

## Third-kind extension

The new differential \(\omega_2=p^2dp/Z\) is meromorphic on the compact curve.
At \(u=1/p\), put \(Z=u^{-3}V\). Then

\[
 V^2=-4+C^2u^4+2HCu^5+H^2u^6,
 \qquad \omega_j=-u^{1-j}du/V.
\]

For either infinity section \(V(0)=s\), \(s^2=-4\), one has
\(V^{-1}=s^{-1}+O(u^4)\). The compact basis forms \(j=0,1,3,4\) have residue
zero, while \(\omega_2\) has residue \(-1/s\). These two opposite residues
are independent of both parameters. Thus the two parameter derivatives of
\(\omega_2\) lie in the compact rank-four cohomology and the new connection
has a zero fifth row. Its two compact columns and exact \(d_p(R/Z)\) terms
passed the independent cleared Dwork identities.

For a five-component current with physical base components \(a_x,a_y,a_z\),
the fifth equation is exactly

\[
\partial_xa_{x,2}+\partial_ya_{y,2}+\partial_za_{z,2}=0.
\]

This is necessary to cancel the residues of the current differential, since the
physical source \(\nabla_H\omega_0\) has zero residue. It is not necessary to
set every \(a_{i,2}\) to zero: a nonzero divergence-free residue current is
allowed. The compact equations retain the new columns, so they can supply an
additional construction beyond the compact rank-four search.

These poles are compatible with the certificate's rational localization.
Under \(p=ab,Z=b^6-a^6\), the new differential is a rational physical form.
The polynomial \(Z\) is coprime to the physical \(F\): its complex factors
are \(b-\zeta a\), \(\zeta^6=1\), and no such factor divides \(F\), whose
restriction to that hyperplane retains the nonzero \(X_0^6\) coefficient.
Any nonzero base denominator is legal by monicity in \(X_2\). Introducing a
third-kind form therefore imposes no new prohibited \(F\)-pole. The quotient
curve field embeds into the physical field through these rational formulas;
an exact primitive constructed on the quotient pulls back exactly. If a
construction first adjoins further coefficient extensions, trace/descent must
still be supplied separately.

A successful cohomological current must retain the explicit exact Dwork terms
when producing a rational differential primitive, and must then verify the full
physical cleared identity, homogeneous degrees, nonzero denominator and
coprimality. No rational current or certificate is established by these checks.
They are independent exact algebraic verification, not protected Lean
verification.
