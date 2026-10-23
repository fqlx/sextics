# Exact trace-free root-log family

This is a constructive normalization of closed one- and two-forms. It is
not a completed primitive. Use the cubic field and physical symplectic
form from `cubic-poisson-witness-interface.md`.

Put
\[
 r=-Cp^3/H=1+Bp/H,\qquad \kappa=B^3/(CH^2),\qquad
 F=\frac1{1+2r}=-\frac H{pg}.
\]
Then
\[
 (r-1)^3+\kappa r=0,\qquad
 4\kappa+27=\frac{(1+2r)^2(4-r)}r,\qquad
 R=\frac{r(r-1)}{CH(1+2r)^3}.
\]
The trace of \(F\) is exactly one. Thus \(F-1/3\) and \(dF\) are
trace-free. The normalized logarithmic one-forms simplify to
\[
 \alpha_p=d\log p-\tfrac13d\log(H/C)=\tfrac13d\log r,
\]
\[
 \alpha_g=d\log g-\tfrac13d\log\Delta
 =\tfrac13d\log\frac{1+2r}{4-r}
 =\frac{3\,dr}{(1+2r)(4-r)},
 \qquad \Delta=4B^3+27CH^2.
\]
They are closed and trace-free, but
\(\alpha_p\wedge\alpha_g=0\): both are multiples of \(dr\).
The exact higher-pole part satisfies the nontrivial identity
\[
 \boxed{\alpha_g=\frac{81}{4\kappa+27}\alpha_p+3\,dF,\qquad
 CH\,R\,d\log\kappa=-\tfrac12dF.}
\]
The coefficient \(1/(4\kappa+27)\) retains its double zero at the
ramification root \(r=-1/2\); it is not a pole-free logarithmic replacement.

## Closed two-forms serving the entire source

For any closed rational base one-form \(\eta\), the two-form
\[
 \beta_\eta=-\tfrac12dF\wedge\eta
\]
is closed and trace-free, including its actual higher-pole part. With
\(\pi\) the physical Poisson tensor,
\[
 \beta_\eta\wedge\omega
 =CH\,R\,\pi(d\log\kappa,\eta)\,\Omega.
\]
Consequently a closed rational one-form satisfying
\[
 \boxed{\pi(d\log\kappa,\eta)=1/(CH)}
\]
would give the actual primitive \(\theta\wedge\beta_\eta\), where
\(d\theta=\omega\). No such one-form has been found.

Absolute closedness can be weakened to
\(d\kappa\wedge d\eta=0\). In particular, if the \(\eta_j\) are closed,
then \(\eta=\sum_j a_j(\kappa)\eta_j\) still produces a closed
\(\beta_\eta\) for arbitrary rational functions \(a_j\). This is a
linear-span problem over \(\mathbf Q(\kappa)\), rather than only over
constant coefficients. It retains the full physical time condition.

There is a broader actual current criterion. A physical base vector
\(V\) satisfying
\[
 \operatorname{div}_{\rho}V=0,\qquad
 V(\log\kappa)=-1/(2CH)
\]
would give the trace-free current \((F-1/3)V\) serving \(R\). This requires
only one coefficient-flow constraint and permits all three of \(H,B,C\)
to vary. It does not follow from the universal coefficient primitive.

## A closed correction to the Hamiltonian pole reduction

Use component-defined
\(N=(3z^2f_U,-3z^2f_z,6tf_t,-6tf_K)\), and let
\(Q=\{f,g\}_{\rm base}\), with \(p\) held constant in the base bracket.
Then
\[
 \left\{\frac{p^2}{2Q},\log Q\right\}
 =\frac{pN(Q)}{Q^2g}.
\]
The left side uses only the rational differential \(dQ/Q\); its closed
two-form is equivalently
\(d(p^2/2)\wedge d(-1/Q)\). Thus, after the global branch-pole correction
constructed in the Jacobian notes, this explicit closed two-form cancels
the \(2N(Q)\) part of that correction. Its remaining scalar is
\[
 -\frac{p^2\{g,Q\}_{\rm base}}{2Q^2g}.
\]
This is regular at a generic point of \(g=0\) as a four-form, but the
\(Q\) poles remain and no primitive is asserted for them.

Prepared with OpenAI Codex assistance.
