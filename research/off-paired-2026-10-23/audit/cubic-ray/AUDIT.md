# Independent cubic-ray audit and completeness scope

`verify_finite_fraction.py` passes 49 exact identities using Python's standard
library `Fraction`, polynomial dictionaries, and univariate reduction modulo
\(s^3+(B/C)s+H/C\). It imports neither the connection generator nor SymPy.
The checked data hash is recorded in `finite-fraction-results.json`.

The checks include the inverse normal derivative, all six basis derivatives,
all twelve flatness entries, both scaling identities, the physical source,
its second-\(H\)-derivative description, the trace pairing and determinant,
the universal Möbius identities, \(W_2(F_0)=R\), and \(\operatorname{Tr}F_0=0\).
The basis shift \(e_2=s^2+2B/(3C)\) and its parameter derivatives are retained.
Columns mean derivatives of basis elements, so coefficient columns carry
\(\partial_i+M_i\). No sign or transpose discrepancy was found.

`verify_physical_fraction.py` passes 56 further exact polynomial/Laurent
identities for the two physical coordinate maps, sources, Piola matrices,
normal jets, low-degree density, and the Nambu correction. Neither script
constructs a current for the fixed source.

## Why the finite rank-two current is complete

For the unrestricted complex-coefficient contract, take the constant field
\(k=\mathbb C\). The same formulas can be used over \(\mathbb Q\) for
rational-coefficient searches; using \(k=\mathbb Q\) alone should not be
described as averaging arbitrary complex constants into \(\mathbb Q\).

In the first chart let
\[
K=k(x,a,u,v),\quad L=K[s]/(Cs^3+Bs+H).
\]
The physical field is \(L(y)\), with \(y^2=s\), and the simultaneous
\(Y\)-sign involution fixes precisely \(L\). The cubic is irreducible and
separable for this target: it comes from the irreducible physical sextic by
the invertible monomial chart substitution, and its discriminant is nonzero.
Absolute irreducibility of the physical sextic also follows from its known
smoothness. The elementary maximal-coordinate gradient estimate has mixed
derivative coefficient bounds
\((13/6,7/3,5/6,5/6,1,5/6)\), all strictly less than 6; projective factors
would intersect and produce a singular point.

The physical source is invariant under the sign involution. Any rational
three-form primitive can therefore be averaged and descended to \(L\).
Because \(L/K\) is finite separable in characteristic zero, its differential
one-forms have basis \(dx,da,du,dv\) over \(L\). Every rational three-form
on this field consequently has a unique expression
\[
\eta=\sum_i a_i\,\iota_{\partial_i}(dx\wedge da\wedge du\wedge dv),
\quad a_i\in L.
\]
Its derivative is \((\sum_iD_i a_i)\mu\), where
\(D_i=\partial_i-f_i\partial_s/g\) and \(g=3Cs^2+B\).
Thus allowing all four base directions and arbitrary rational coefficient
functions exhausts rational three-form primitives on this chart.

The field trace commutes with these derivations. The actual source
\(R=Bs/g^3=-B\,D_H^2s/(6C)\) has trace zero. Replacing each coefficient
by \(a_i-\operatorname{Tr}(a_i)/3\) therefore preserves its derivative.
The trace-free field is two-dimensional over \(K\), with basis
\(s,s^2+2B/(3C)\). Every field element has this representation after trace
projection, including elements originally written with arbitrary poles in
\(s\): inverses reduce modulo the cubic and become rational base
coefficients. This is a finite algebra of functions, not a compact-curve
cohomology truncation. It removes no allowed endpoint pole or denominator
degree. It does not make the resulting rational PDE automatically solvable.

For the full-G36 low-degree map, the exponent determinant is +36. Its kernel
is the order-36 diagonal torus group, and the source descends exactly.
Averaging over this finite group gives the same completeness statement on
the low-degree cubic field, now with the scalar density below. As before,
restricting coefficient denominators or base directions would be an additional
search ansatz, not the complete equation.

## Source, orientation, and the normal Jacobian

The high-degree chart gives
\[
\frac{y^3\,dx\wedge da\wedge dy\wedge dY_1\wedge dY_2}{F^2}
=\frac{s^2\,dx\wedge da\wedge ds\wedge du\wedge dv}{2f^2}.
\]
Moving the normal differential \(df\) past \(dx,da\) has positive sign.
Its double-pole residue with \(df\) first is
\[
\frac1g\partial_s\left(\frac{s^2}{2g}\right)\mu
=\frac{Bs}{g^3}\mu.
\]
The derivative of \(1/g\) is necessary. Dropping it would change the source
to \(s/g^2\). The source orientation here is positive, unlike the earlier
quartic convention where the normal differential crossed only one base
differential.

The low-degree map has
\[
J=36a^6x^2/y,\qquad
\frac{A}{J}=\frac{p^2}{36tz^2}
=\rho\frac{p^2}{2},\quad \rho=\frac1{18tz^2}.
\]
Here \(dp\) crosses four preceding quotient differentials, again positive.
The residue is \(\rho R\,dz\wedge dU\wedge dK\wedge dt\). Writing the
current as \(\rho\sum a_i\iota_i\mu\) gives the exact weighted equation
\[
\sum_i(D_i a_i+\ell_i a_i)=R,
\quad (\ell_z,\ell_U,\ell_K,\ell_t)=(-2/z,0,0,-1/t).
\]
The density is base-rational, so trace projection still preserves this
weighted equation.

## Conditional ambient lift

For actual elements \(a_i\in L\) with \(\sum_iD_i a_i=R\), choose ambient
rational representatives whose denominators are nonzero modulo \(f\), and set
\[
V_{q_i}=-g a_i,\qquad
V_s=\frac{s^2}{2g}+\sum_i f_i a_i.
\]
Exact product differentiation, retaining \(\partial_s f_i=\partial_i g\),
gives
\[
V(f)=s^2/2,\qquad
\operatorname{div}V=g\left(R-\sum_iD_i a_i\right).
\]
Hence the divergence vanishes modulo \(f\), giving the complete certificate
identity after denominator clearing. For the low-degree weighted equation,
multiply this entire field by \(\rho\); its divergence becomes
\(\rho g[R-\sum_i(D_i a_i+\ell_i a_i)]\).

The ordinary Piola pullback \(J(d\theta)^{-1}V\) preserves the entire
divergence identity and sends the source to \(y^3\). The first chart's
matrix was checked at all 25 independent first-jet entries and all five
zero-order entries. All coordinate monomials removed by the chart are legal
denominator factors because none divides the immutable sextic. Other rational
representatives must have denominators nonzero in the cubic field; after
pullback and clearing they are nonzero on the generic physical hypersurface.
Together with absolute irreducibility, this gives complex coprimality.
Every candidate must still undergo the exact cleared polynomial identity,
homogeneity and admissibility checks before formal submission.

## Universal Möbius flow and the remaining physical obligation

The exact universal identities
\[
W_2=-\frac{2B^2}{3C}\partial_H+3H\partial_B,
\quad F_0=\frac{3Cs^2-B}{10g^3},\quad W_2(F_0)=R,
\quad\operatorname{Tr}F_0=0
\]
are correct. They integrate the actual scalar source in coefficient space.
The physical lift must still preserve the actual base volume.

Root's \(N_2,J,K\) formulas pass all independent checks:
\(\operatorname{div}N_2=\operatorname{div}K=0\), \(K(H)=K(B)=K(C)=0\),
and \(N_2/J\) lifts \(W_2\). Its divergence is
\(-N_2(J)/J^2\), which is nonzero. Therefore
\[
K(h)=N_2(J)/J^2
\]
has exactly the displayed sign. Such a rational scalar solution would give a
divergence-free lift and a valid current \(a_i=F_0V_i\). It is sufficient
for that chosen universal flow; the complete rank-two current equation is
broader. No solution of this scalar equation or the full current equation is
established here.
