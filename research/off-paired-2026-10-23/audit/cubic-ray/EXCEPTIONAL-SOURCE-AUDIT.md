# Independent exceptional-surface and first-normal-jet audit

The weighted graph calculation produces a genuine exceptional surface with
four invariant holomorphic two-forms. Its elliptic maps, source character,
actual leading target normal jet and stated rational-lift derivatives are
correct. No global closed extension or source Gysin coefficient has been
established. The first derivative of a tentative rational lift is not yet an
intrinsic Kodaira--Spencer calculation.

## Exact model and physical normal source

For the Y graph pair \((Y_0,Y_1)\), set
\(Y=\epsilon(a,1,b)\), with full
\(M_0=m_{01}a+m_{12}b+m_{02}ab\). Substitution in the exact graph divisor
and original sextic gives

\[
D_{18}=\epsilon^{14}\bigl[
\epsilon^4(1+a^6+b^6)((1+a^6)^2-16a^6)-16a^6M_0\bigr].
\]

The weighted substitution \(\epsilon=t^3,a=t^2A\) gives exactly the
\(t^{54}\) strict model in the constructive note. Its residual
\((t,A)\mapsto(\omega t,\omega A)\) fixes all three original Y
coordinates. The quotient invariant \(w=4A^3b\) gives, on \(X_1=1\),

\[
z^6+x^6+1=0,\qquad (x/2)w^2=b^7+b,
\quad x=X_2,z=X_0.
\]

The original projective volume on this chart is
\(-dz\wedge dx\wedge dY_0\wedge dY_1\wedge dY_2\). For
\(A_{\rm target}=z^3Y_0^3\), putting the F normal first at \(z\) gives
the exact coefficient

\[
\frac{A_{\rm target}F_{zz}-(\partial_zA_{\rm target})F_z}{F_z^3}.
\]

The numerator derivative is essential. Its leading coefficient at \(Y=0\)
is \(Y_0^3/(18z^8)\). The exact three-Y Jacobian in order \((t,A,b)\)
is \(-3t^{10}\), so the fixed orientation gives the leading source

\[
-\frac{t^{25}A^3}{6z^8}\,dx\wedge dt\wedge dA\wedge db.
\]

All these calculations were checked from the full immutable affine \(F\),
including both mixed terms containing \(z\). Higher normal jets have not
been discarded.

## Holomorphic forms and complete target character

The surface is dominated by

\[
C':\quad z^6+64\xi^{12}+1=0,\quad x=2\xi^2,
\qquad G:\quad y^2=b^7+b,\quad y=\xi w.
\]

The simultaneous \((\xi,y)\mapsto(-\xi,-y)\) quotient recovers the
surface function field. The whole maps to the fixed \(j=1728\) elliptic
curve are

\[
U_C=8\xi^6,\quad V_C=2\sqrt2i\,\xi^3z^3,
\qquad U_G=b^3,\quad V_G=by.
\]

Both satisfy \(V^2=U^3+U\). Their nonzero invariant differentials pull
back to the coefficients in the constructive note. Their product equals
\(9/(8\sqrt2i)\) times

\[
\gamma=\frac{dx\wedge db}{z^3A^3}
=\frac{4b\,dx\wedge db}{z^3w}.
\]

It is a nonzero holomorphic two-form on a resolution: upstairs it is a
product of holomorphic elliptic differentials, invariant under the
simultaneous involution. The quotient's fixed-point singularities are
ordinary double points, across which that invariant two-form extends.

For completeness, \(C'\) has genus twenty-five. Its anti-invariant
holomorphic one-forms are

\[
\xi^{i-1}d\xi/z^j,\qquad i\text{ odd},\quad
1\le j\le5,\quad 1\le i<2j.
\]

The inequalities follow by checking the finite branch points and the six
points at infinity; they give fifteen forms. The three forms
\(b^l db/y\), \(0\le l\le2\), on \(G\) give forty-five product forms
in the simultaneous-sign quotient. Applying the two character congruences
leaves exactly the four triples

\[
(i,j,l)=(1,2,0),(1,5,0),(3,3,1),(5,4,2).
\]

Their rational coefficients are respectively
\(r/(xbz^2),r/(xbz^5),r/z^3,rxb/z^4\), where \(r=4b/w=1/A^3\).
The independent audit checks the full order-six generators of G36 directly.
The paired sign on all Y coordinates, implicit in the note's order-three
generator, acts trivially on this exceptional surface. There is therefore
no missing character check.

The actual target rational form is itself invariant: its polynomial
numerator has character \((3,0)\), and the projective volume also has
character \((3,0)\). Their sum is zero modulo six. Thus invariance is
the right necessary source character. It does not identify a Gysin image
within the twenty-four-dimensional target polynomial source space.

## The first rational-lift derivative and its limits

The quotient-free global chart retains both exact equations

\[
16M_0=r^2C_0K_0,\qquad
16H_X=-r^3a^3C_0(1+a^6)^2,
\]

with \(C_0=1+b^6+a^6\), \(K_0=(1+a^6)^2-16a^6\) and the full \(M_0\).
At \(a=0\), fixing \(x,b\), these give

\[
z_a=0,\qquad
\frac{r_a}r=\frac{z^3/2+z^2xb/3}{xb}
\]

on the chart \(zxb\ne0\). For the third tentative form this yields

\[
\partial_a(r\,dx\wedge db/z^3)
=r\left(\frac1{2xb}+\frac1{3z}\right)dx\wedge db.
\]

The first term is exactly \(d(4\,db/w)\), since the exceptional equation
implies \(w_x=-w/(2x)\). The second equals

\[
\frac43(\xi\,dx/z)\wedge(b\,db/y).
\]

Also, the tentative fourth-minus-three-halves-third combination has derivative
\(rxb\,dx\wedge db/(3z^2)\) modulo \(d(-6\,db/w)\). These are exact
computations for the displayed rational lifts. They do not show that those
lifts extend as holomorphic relative forms on a proper model. Consequently
their remaining terms must not yet be called an intrinsic KS obstruction
or a proof that every compatible linear combination fails to extend.

The missing positive step remains a legitimate closed extension of an
appropriate exceptional two-form through the full graph family, followed
by an actual target-source Gysin computation. Finite algebraic adjunction
of unrelated constant curve roots supplies no descent or nonzero trace
argument for that step.

`verify_exceptional_fraction.py` independently passed twenty-six audit groups
using standard-library Fraction polynomial/Laurent arithmetic and exact curve
relations, without importing the primary SymPy checker. No certificate has
been found.
