# Exact source direction carried by the moving third-kind kernel

Use the actual endpoint curve and moving pole

\[
 Z^2=(H+Cp)^2-4p^6,\quad s=-3z/2,\quad L=H+sC,
 \quad V_s^2=L^2-4s^6.
\]

At fixed \(L,z\), both \(s,V_s\) are fixed. For the normalized
third-kind differential

\[
 \eta_s=\frac{V_s\,dp}{(p-s)Z},
\]

its residues at the two points above \(p=s\) are \(\pm1\). Exact
differentiation, without a compact-basis reduction, gives

\[
 \boxed{(\partial_C-s\partial_H)\eta_s
      =-\frac{V_s(H+Cp)\,dp}{Z^3}
      =V_s\,\partial_H\omega_0.}
\]

The pole factor cancels because
\((\partial_C-s\partial_H)Z=(H+Cp)(p-s)/Z\). Thus this kernel carries
the actual endpoint source direction exactly.

The remaining coefficient cannot be discarded. Let
\(J=\partial(L,C)/\partial(x,y)\), \(\phi=y^3/J\), so that
\(y^3dx\wedge dy\wedge dz=\phi\,dL\wedge dC\wedge dz\).
On the fixed-\(L,z\) coefficient curve,

\[
 \phi\,dC=-\frac{dx}{6y^2}.
\]

The minus sign corresponds to this displayed \(dL\wedge dC\) orientation.
Multiplication of \(\eta_s\) by \(\phi/V_s\) leaves the exact
\(C\)-derivative correction \((\phi_C/V_s)\eta_s\). It also gives a
nonzero residue derivative unless a full divergence-free base current or
an equivalent residue contraction cancels it. A primitive for the endpoint
source direction alone is therefore not a primitive for the physical
source.

The coefficient curve admits the exact elliptic decompositions in the
neighboring notes, but \(C=tz/2+u/3\) changes under the intermediate
\(u\mapsto-u\) quotient. The entire endpoint kernel and its connection
must be transported or retained; replacing only its scalar density by an
elliptic differential loses that dependence.

No rational current cancelling this coefficient/residue correction has
been found. These formulas give a concrete constructive obligation rather
than a bounded nonexistence claim.
