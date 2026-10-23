# Exact rational normal decomposition of the physical coefficient

This is a constructive identity, not a certificate or a primitive for the actual four-form. All coefficients are rational and the two supplied SymPy checks pass.

On the physical base put

\[
a=x^3,\quad q=3C-\frac32az=xy,\quad
P=a^4+q^6+a^2(z^6+qz/2+1-H).
\]

Differentiating with $C,z$ fixed on $P=0$ gives $a_H=a^2/P_a$. The coordinate Jacobian and target density are exactly

\[
\det\frac{\partial(H,C,z)}{\partial(x,y,z)}=P_a/a,
\qquad y^3\,dx\wedge dy\wedge dz=\phi\,dH\wedge dC\wedge dz,
\qquad\phi=q^3/P_a.
\]

The rational function

\[
R=-\frac{27C^3}{a}+\frac{81}{4}Cz^2a-\frac{27}{16}z^3a^2
\]

satisfies

\[
\frac{q^3}{a^2}\,da=dR-\frac{81}{2}C^2z\,d\log a
\pmod{dC,dz}.
\]

Equivalently,

\[
\phi=R_H-\frac{81}{2}C^2z\,(\log a)_H.
\]

The last display abbreviates rational derivatives: $(\log a)_H=a/P_a$. A logarithm is not an allowed certificate coefficient. The identity exposes an explicit logarithmic residue; it does not cancel the nonzero $\phi_H$ correction. Integrating the rational part by parts against the endpoint Gauss–Manin form introduces second $H$ derivatives of that form, so it may be useful in a full rank-four current ansatz.

The corrected derivative formula is

\[
\phi_H=\frac{(2aq^3+3a^2q^2q_a)P_a-a^2q^3P_{aa}}{P_a^3},
\qquad q_a=-3z/2.
\]

Neither this expression nor its logarithmic-residue summand is silently discarded.

A polynomial-curve construction varying $q$ with $a,z$ fixed would fix two original-coordinate ratios after finite extension, placing it in an already excluded relative-primitive scope. A source-carrying construction must vary $a$ or $z$ as well, or use the remaining coefficient currents.
