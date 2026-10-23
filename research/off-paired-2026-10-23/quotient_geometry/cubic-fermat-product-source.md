# The exact cubic source over a fixed Fermat product

This is a source-carrying normalization for a possible CM contraction. No
contraction or rational primitive is asserted.

Use the pre-diagonal cubic coordinates in `../cubic-ray/INTERFACE.md`:
\[
 H=1+x^6+a^6,\quad C=1+u^6+v^6,\quad
 B=xu/2+x^3auv/2+xav/3,
\]
\[
 H+Bp+Cp^3=0,\quad g=3Cp^2+B,\quad R=Bp/g^3.
\]
The physical residue is \(R\,dx\wedge da\wedge du\wedge dv\).

On the finite extension \(\alpha^6=H-1\), \(\beta^6=C-1\), set
\[
 x=\alpha\xi,\quad a=\alpha\eta,\quad
 u=\beta\nu,\quad v=\beta\varpi,
 \qquad \xi^6+\eta^6=\nu^6+\varpi^6=1.
\]
The two Fermat curves are now fixed. The actual coupling is still
\[
 \boxed{B=\frac{\alpha\beta}{2}\xi\nu
 +\frac{\alpha^4\beta^2}{2}\xi^3\eta\nu\varpi
 +\frac{\alpha^2\beta}{3}\xi\eta\varpi.}
\]
In the orientation \((H,C,\xi,\nu)\), the exact physical volume is
\[
 \boxed{dx\wedge da\wedge du\wedge dv
 =-\frac{\alpha^{-4}\beta^{-4}}{36}
 dH\wedge dC\wedge\frac{d\xi}{\eta^5}
                         \wedge\frac{d\nu}{\varpi^5}.}
\]
Thus the entire source is this volume times \(R\), with \(p\) satisfying
the displayed cubic using the boxed rank-three coupling. The two curve
one-forms are holomorphic and nonzero.

A source-carrying CM contraction must retain the three different
\((\alpha,\beta)\) weights \((1,1),(4,2),(2,1)\), the cubic variable
\(p\), and both \(H,C\) directions. Replacing \(B\) by an independent
coefficient or integrating a density only on the two fixed curves would
omit part of this source. The finite sixth-root extension is harmless
only after constructing a genuine primitive, when constant field trace
can descend it.

The new full-diagonal quotient symplectic frame described in
`../geometry/potential-current/cubic-current/` is a complementary way to
keep the four-dimensional physical volume during such a construction.

Prepared with OpenAI Codex assistance.
