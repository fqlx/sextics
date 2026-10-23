# Independent closed-two-form audit and complete conditional interface

No correction cancelling the remaining source is supplied. The fixed target
remains unsolved. The computations here use the actual G36 chart, the physical
volume, and derivatives in the cubic function field.

Let

\[
q=(z,U,K,t),\quad H=1+z^2+t,\quad
B=U/2+K/3+zUK/2,\quad C=z^{-2}+U^6+K^6/t,
\]
\[
f=H+Bp+Cp^3=0,\quad g=B+3Cp^2,\quad
R=Bp/g^3,\quad \rho=(18tz^2)^{-1},
\]
\[
\omega=\frac{dz\wedge dU}{3z^2}+\frac{dK\wedge dt}{6t},
\quad \Omega=\omega^2/2=\rho\,dz\wedge dU\wedge dK\wedge dt.
\]
The constant field is \(\mathbb C\) for the unrestricted contract; the
displayed constructions and audit arithmetic are defined over \(\mathbb Q\).
All unmarked differentials and brackets are absolute in
\(L=\mathbb C(q)[p]/(f)\), so \(D_i p=-f_i/g\).

## A complete closed-two-form criterion

The rational one-form

\[
\theta=-\frac{dU}{3z}+\frac{K\,dt}{6t}
\]

satisfies \(d\theta=\omega\). Thus any rational two-form \(\beta\) satisfying

\[
d\beta=0,\qquad \beta\wedge\omega=R\Omega
\]

gives an actual rational primitive \(\eta=\theta\wedge\beta\).
This criterion is complete when all rational two-forms are allowed: if
\(d\eta=R\Omega\), the symplectic linear isomorphism
\(\lambda\mapsto\lambda\wedge\omega\) from one-forms to three-forms writes
\(\eta=\lambda\wedge\omega\). Then \(\beta=d\lambda\) is closed and has
the required trace. Restricting the coefficients or denominators of
\(\beta\) gives a restricted search family.

Write \(\beta=\sum_{i<j}\beta_{ij}\,dq_i\wedge dq_j\), with indices
\(0,1,2,3=(z,U,K,t)\). Its symplectic trace is

\[
\Lambda\beta=3z^2\beta_{01}+6t\beta_{23}.
\]

Closure means all four identities

\[
\begin{aligned}
c_{012}&=D_0\beta_{12}-D_1\beta_{02}+D_2\beta_{01}=0,\\
c_{013}&=D_0\beta_{13}-D_1\beta_{03}+D_3\beta_{01}=0,\\
c_{023}&=D_0\beta_{23}-D_2\beta_{03}+D_3\beta_{02}=0,\\
c_{123}&=D_1\beta_{23}-D_2\beta_{13}+D_3\beta_{12}=0.
\end{aligned}
\]

The corresponding current \(\iota_a\Omega=\theta\wedge\beta\) is

\[
a=\frac1\rho\left(
-\frac{\beta_{23}}{3z}+\frac{K\beta_{12}}{6t},
-\frac{K\beta_{02}}{6t},
\frac{\beta_{03}}{3z}+\frac{K\beta_{01}}{6t},
-\frac{\beta_{02}}{3z}\right).
\]

The independent generic-jet check gives the full defect, before imposing
closure:

\[
\sum_i D_i(\rho a_i)-\rho\Lambda\beta
=-\frac{c_{023}}{3z}+\frac{Kc_{012}}{6t}.
\]

Thus the source sign is positive. The current can be passed directly to the
ambient and physical Piola lift in
[POISSON-TO-WITNESS.md](POISSON-TO-WITNESS.md), with no additional sign.

For rational nonzero \(h,k\), the two-forms
\(dF\wedge dh/h\) and \(dh/h\wedge dk/k\) are closed. Their traces are
respectively \(\{F,h\}/h=\{F/h,h\}\) and
\(\{h,k\}/(hk)\). These are rational forms; they introduce no logarithmic
coefficient functions. The second family can be used even when its rational
de Rham class is nonzero, since the explicit \(\theta\) still gives the
required primitive after its trace is matched. Neither family by itself has
been shown to span a source-carrying correction.

## Audit of the new actual partial current

Use the left convention \(X_F(G)=\{F,G\}\), so
\(\iota_{X_F}\omega=-dF\). For base brackets with \(p\) held fixed, put

\[
A=\{H,B\}_0,\quad D=\{H,C\}_0,\quad E=\{B,C\}_0,
\quad Q=A+3p^2D+2p^3E.
\]

The nonlinear vector field fixed by its components is

\[
N=(3z^2 f_U,-3z^2 f_z,6t f_t,-6t f_K)=gX_p.
\]

In particular \(Np=0\), \(Ng=-Q\),
\(\operatorname{div}_{\Omega}N=-Q/g\), and
\(\iota_N\Omega=-g\,dp\wedge\omega\). Calling this field a left
Hamiltonian field of the ambient \(f\) without specifying held-fixed
derivatives would reverse the sign.

The audited absolute rational potential is

\[
\widetilde\lambda=-\frac{p^2(dB+3p^2dC)}{2Qg}.
\]

Direct differentiation, including all base and implicit \(p\) derivatives
of \(Q\), gives

\[
d\widetilde\lambda\wedge\omega
=\left(R-\frac{p^2\{g,Q\}_0}{2Q^2g}\right)\Omega.
\]

This was checked independently by clearing \(2Q^2g^3\) in the direct
bracket trace, as well as by checking the first potential and the subsequent
closed \(Q\)-log correction separately. The old remaining term
\(-p(2NQ+p\{g,Q\}_0)/(2Q^2g)\) and the branch-residue primitive signs
also passed. The subscript \(0\) is essential. Treating a relative
\(p\)-constant primitive as absolutely closed discards terms which add back
the original \(R\).

The remainder is nonzero. At \((z,U,K,t)=(1,1,1,2)\), reducing the actual
\(\{g,Q\}_0\) modulo the specialized cubic gives

\[
\frac{103707}{5}p^2+\frac{3778244}{75}p-\frac{73476}{25}\ne0.
\]

## Exact scope of the branch improvement

Let \(J=\det\partial(H,B,C)/\partial(z,U,K)\). Where \(J\ne0\), the
coordinates \((H,B,C,t)\) are valid and on the cover

\[
\Omega=\frac\rho J\,dH\wedge dB\wedge dC\wedge dt
=-\frac{\rho g}J\,dp\wedge dB\wedge dC\wedge dt.
\]

Hence both displayed remaining four-forms with a single scalar \(g\)
denominator are regular at the generic branch on the open set
\(QJzt\ne0\). This assertion concerns the full four-form, not the scalar
coefficient in the original base volume.

An actual simple branch point lies on this open set:

\[
z=1,\quad U=-1,\quad K=0,\quad p^2=1/12,\quad t=p/3-2.
\]

Exact arithmetic in \(\mathbb Q[p]/(p^2-1/12)\) gives
\(f=g=0\), \(g_p=12p\ne0\), \(J=-2\), and
\(Q=-8+5p/6\ne0\). This checks the claimed generic branch chart on the
actual physical cover. It does not control \(Q=0\), \(J=0\), their
intersections, or the chart boundary.

The missing construction is a closed rational two-form whose trace is
\(+p^2\{g,Q\}_0/(2Q^2g)\). No such correction, finite witness, Lean proof,
or certificate is asserted.

`verify_closed_twoform_fraction.py` records 36 independent exact checks in
`closed-twoform-fraction-results.json`, using only the Python standard
library and the independent audit polynomial routines.
