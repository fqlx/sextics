# Independent constant-density and K3 correspondence audit

Both new transformations preserve the actual physical source. Their Jacobian
signs, finite-field descriptions, deck actions, elliptic differentials and
full coefficient functions pass independent exact checks. They provide an
explicit setting for a constructive current, but do not integrate its full
cubic coefficient. No certificate has been found.

## Rational degree-six base cover

Starting from the physical G36 base \((z,U,K,t)\), put

\[
z=1/Z,\quad U=u,\quad K=hv,\quad t=h^6.
\]

In the order \((Z,h,u,v)\), its signed Jacobian is
\(-6h^6/Z^2\). Hence the exact physical volume and coefficient functions are

\[
\Omega=\frac{dz\wedge dU\wedge dK\wedge dt}{18tz^2}
=-\frac13dZ\wedge dh\wedge du\wedge dv,
\]
\[
H=1+Z^{-2}+h^6,\quad C=Z^2+u^6+v^6,\quad
B=u/2+hv/3+huv/(2Z).
\]

The cubic variable \(p\) is unchanged. Thus the source is exactly

\[
-\frac13\frac{Bp}{(B+3Cp^2)^3}\,dZ\wedge dh\wedge du\wedge dv.
\]

The base extension has degree six, since \(h^6-t\) is irreducible over
the rational base field by the \(t\)-valuation. The inverse formulas are
\(Z=1/z,u=U,v=K/h\). This is a degree statement about the rational base;
no additional exact degree after arbitrary algebraic base changes is needed.
Over \(\mathbb C\), all six automorphisms
\(h\mapsto\zeta_6h,v\mapsto\zeta_6^{-1}v\) fix the complete \(H,B,C\),
the volume and \(p\). Normalized finite field trace can descend any actual
primitive of the pulled-back source over a common finite function field.
It does not descend arbitrary complex constants to \(\mathbb Q\).

The new standard symplectic form
\(\omega_0=dZ\wedge dh+du\wedge dv\) has a constant multiple of the
physical volume. Its Hamiltonian fields therefore preserve that volume.
The checked coefficient brackets include

\[
\{H,C\}=-12Zh^5,
\]

with all full \(B\)-brackets as displayed in the constructive packet.
This symplectic form is a new convenient choice; it need not equal the
pullback of the earlier symplectic form to give the same divergence.

## Common finite field and two fixed elliptic curves

Here \(c\) denotes a sixth root \(c^6=C\), distinct from the third root
used in the earlier Cardano incidence. Normalize

\[
Z=c^3Y,\quad u=cU,\quad v=cV,\qquad
Y^2+U^6+V^6=1.
\]

On \(V\ne0\), let \(T=U/V\), and adjoin

\[
w^3=1+T^6,\qquad e=wV^2,
\quad Y^2=1-e^3,\quad V^2=e/w.
\]

This common angle field is at most degree three over the normalized K3
field, since only \(w\) is adjoined there. The normalized surface has the
usual weighted sextic K3 compactification.

The two fixed elliptic curves are

\[
E_1:\quad y_1^2=e_1^3-4,\qquad
e_1=w^2/T^2,\quad y_1=(T^6-1)/T^3,
\]
\[
E_2:\quad Y^2=1-e^3.
\]

The inverse field description uses

\[
b^2=e_1,\quad T^3=(y_1+b^3)/2,\quad w=bT,\quad V^2=e/w.
\]

It proves a degree bound of twelve over the elliptic product field. No
claim that all these degree bounds are equalities is necessary. The first
elliptic map is nonconstant in \(T\); the second uses the independent
coordinate \(e\), so the correspondence is generically dominant.

The exact differentials, including their factor two, are

\[
\eta_1=\frac{de_1}{2y_1}=\frac{dT}{w},\quad
\eta_2=\frac{de}{2Y},\quad
\frac{dU\wedge dV}{Y}=\eta_1\wedge\eta_2.
\]

The complete four-coordinate Jacobian, using the extended separable
derivations of \(w,Y,V\), gives

\[
\Omega=-c^4dc\wedge dh\wedge\eta_1\wedge\eta_2.
\]

In particular the actual source is

\[
-c^4\frac{Bp}{(B+3c^6p^2)^3}\,
dc\wedge dh\wedge\eta_1\wedge\eta_2
=-\frac W{c^2H}\,dc\wedge dh\wedge\eta_1\wedge\eta_2,
\]

where \(W=HC\,R\), and the full functions are still

\[
H=1+c^{-6}Y^{-2}+h^6,\qquad
B=cV(T/2+h/3)+\frac{hTV^2}{2cY},\qquad C=c^6.
\]

The sixth-root deck action sends
\(c\mapsto\zeta_6c,Y\mapsto\zeta_6^{-3}Y,
V\mapsto\zeta_6^{-1}V,e\mapsto\zeta_6^{-2}e\), fixing \(T,w,h\).
It fixes all physical coordinates and the full source. The additional
K3 cover deck action \(w\mapsto\zeta_3w,e\mapsto\zeta_3e\), fixing
\(V,T,Y,c,h\), has opposite characters on \(\eta_1,\eta_2\). Their
product, the physical coefficients and the source remain invariant.

## Concrete constructive use and the missing obligation

There is a useful simplification besides the density factorization. Exact
rational normal fields for \((H,C)\) are

\[
V_{H,0}=\frac1{6h^5}\partial_h,\qquad
V_{C,0}=\frac1{2Z}\partial_Z+\frac1{6Z^4h^5}\partial_h.
\]

They satisfy \(V_{H,0}(H,C)=(1,0)\) and
\(V_{C,0}(H,C)=(0,1)\). The field

\[
K_0=6v^5\partial_u-6u^5\partial_v
\]

fixes \(H,C\), and its full nonzero \(B\) drift is

\[
J_B=K_0(B)=3v^5+3hv^6/Z-2hu^5-3hu^6/Z.
\]

Thus \(V_B=K_0/J_B\) is a rational \(B\)-normal field. Correcting
\(V_{H,0}\) and \(V_{C,0}\) by their \(B\) drifts times \(V_B\) gives an
explicit three-coefficient normal frame. This makes the full coupled current
equations concrete with relatively small rational denominators. Its divergence
corrections must still be solved; the pure-component moment obstruction
continues to exclude shortcuts that set the required couplings to zero.

An actual rational current or primitive on the common finite cover, retaining
the displayed \(H,B,p\), would be a valid positive result and could be traced
back to the physical source. A CM graph or a primitive for only the product
volume does not provide that current. In particular \(B\) depends on the
finite branch variables \(T,V\), \(H\) depends on the second elliptic point,
and the cubic source retains its standard trace-free character. Tracing away
those variables without tracking the source can lose exactly the needed
coefficient. Any proposed elliptic correspondence must therefore include a
source-carrying lift through the actual cubic field and its mixed derivatives.

`verify_constant_k3_fraction.py` passed 44 independent exact checks using
standard-library Fraction Laurent arithmetic and triangular field reduction.
It imports neither primary construction script nor its Groebner code. The
checked data include the exact source sign, finite-deck coverage, all physical
coefficients, elliptic differentials, full Jacobian and the normal fields
above. These identities are constructive input, not a served kernel or a
proof that the remaining source class vanishes.
