# Independent Cardano/Fano source and rational-cover audit

The new incidence carries the actual physical source with the stated
three-normal numerator. Its first exact elliptic primitive leaves the stated
double-normal correction. The Fano property supplies no primitive by itself;
the boundary poles and parameter jets remain necessary. No certificate has
been found.

## Normal Jacobian and source sign

Let \(q=(x,a,u,v)\) be the actual four-dimensional base, and use the full
physical \(H,B,C\). On the incidence

\[
G_1=S^3+T^3-H=0,\quad G_2=c^3-C=0,\quad Q=B+3cST=0,
\]

the root \(p=-(S+T)/c\) satisfies the original cubic. Put
\(K=S^2+ST+T^2\) and \(\delta=S^3-T^3\). Direct determinant and source
calculation give

\[
J=\det\frac{\partial(G_1,G_2,Q)}{\partial(S,T,c)}=-27c^3\delta,
\quad g=3cK,\quad
R=\frac{ST(S+T)}{9c^3K^3},
\]
\[
N=JR=-\frac{3ST(S^2-T^2)}{K^2}.
\]

The ordered normals \((G_1,G_2,Q)\) placed before \(dq\) require twelve
transpositions, an even number. Consequently the three-normal residue of
\(N\,dq\wedge dS\wedge dT\wedge dc/(G_1G_2Q)\) is exactly \(+R\,dq\).
The independent checker also retains all \(H_i,B_i,C_i\) terms in the
horizontal derivatives and verifies all three differentiated equations.

## The remaining source with its exact coefficient

The vertical field \(\delta_E=3T^2\partial_S-3S^2\partial_T\) has zero
ambient divergence and fixes \(G_1,G_2\). With

\[
q_E=-\frac{S+T}{2K},
\]

the checked identities are

\[
\delta_E q_E=N,\qquad \delta_EQ=-9c\delta,\qquad
q_E\delta_EQ=\frac{9c}{2}(S^2-T^2).
\]

The exact first term therefore leaves the rational seven-form

\[
\frac{q_E\delta_EQ}{G_1G_2Q^2}\,dq\wedge dS\wedge dT\wedge dc.
\]

For an unambiguous ordered reduction, take the \(Q\)-normal residue first,
holding \(q,S,T\) fixed. Since \(Q_c=3ST\) and moving \(dc\) past six
differentials is even, its scalar is

\[
A_Q=\frac1{3ST}\partial_c
 \left(\frac{q_E\delta_EQ}{3STG_2}\right)
=\frac{q_E\delta(2c^3+C)}{S^2T^2G_2^2}.
\]

The resulting six-form is \(A_Q\,dq\wedge dS\wedge dT/G_1\).
Set \(\tau=ST\), avoiding confusion with other parameters called \(t\).
The Jacobian of \((G_1,\tau)\) in \((S,T)\) is \(3\delta\). Eliminating
\(c=-B/(3\tau)\), put

\[
D=\frac{B^3}{27\tau^3},\qquad G_{\rm eff}=C+D.
\]

Then \(G_2=-G_{\rm eff}\), \(2c^3+C=C-2D\), and taking the \(G_1\)
residue gives the exact remaining five-form

\[
\boxed{\frac{q_E}{3\tau^2}\,
 \frac{C-2D}{(C+D)^2}\,dq\wedge d\tau.}
\]

The cyclic reorder \((G_1,G_2,Q)\to(Q,G_1,G_2)\) is even. The last
\(G_2\) residue remains to be taken; the boxed formula uses a fixed
\(Q\)-first convention rather than switching a pair of normals without
its wedge sign. Moving \(d\tau\) past \(du,dv\) is also even.

The checked parameter identity, with the physical \(X,Y\) held fixed, is

\[
\frac{C-2D}{(C+D)^2}
=-\tau^2\partial_\tau\left(\frac1{\tau(C+D)}\right).
\]

In particular the boxed form contains \(-q_E/3\) times this derivative.
Using it for integration must still retain derivatives of \(q_E\), the
\(S,T\) branch, all base coefficients and any constructed primitive.

## Projective degree and the physical boundary

For the projective \(Y\)-plane, \(C=F_Y\) is degree six and the full
\(B_X(Y)\) is quadratic. Thus \(C-2D\) has degree six. Multiplying its
affine \(Y_0=1\) representative by \(Y_0^3\) gives degree nine, exactly
the numerator degree required for a pole-two plane form:
\(9+3=2\cdot6\).

The relative complete intersection

\[
Q=B_X(Y)+3\tau c=0,\qquad
J_Y=F_Y-c^3-d^3-e^3=0
\]

in weights \((1,1,1,2,2,2)\) has dimension three and anticanonical weight
\(9-(2+6)=1\). Eliminating \(c\) yields
\(d^3+e^3=G_{\rm eff}\). Quasismoothness on the smooth sextic locus is
consistent: all cone derivatives zero would force \(d=e=0\) and a
singular point of the moving plane sextic. That locus is nonempty at the
stated Fermat specialization. This is a quasismooth weighted model; it
does not assert that the coarse projective space is smooth everywhere.

The physical curve is the codimension-two locus \(d=e=0\). With the
positive \((d,e)\)-then-plane order,

\[
\operatorname{Res}_{d=e=0}
 \frac{P_2\,du\wedge dv\wedge dd\wedge de}{J_Y^2de}
=\frac{P_2\,du\wedge dv}{G_{\rm eff}^2}.
\]

The extra \(1/(de)\) is part of the full physical source. Retaining it
also gives the correct global degree: the weighted ambient volume has
weight nine, \(P_2\) has weight nine, and
\(QJ_Y^2de\) has weight \(2+12+2+2=18\). If using the volume after
eliminating \(Q\), its weight is seven and the remaining denominator
weight is sixteen, with the same balance. Merely integrating polynomial
densities on the Fano companion does not remove these boundary factors.

## Rational S3 cover over kappa and its elliptic bridge

With \(q_c=S/T\), direct substitution gives

\[
\kappa=-\frac{27q_c^3}{(q_c^3+1)^2},\quad
F=\frac{q_c^2-q_c+1}{3(q_c^2+q_c+1)},\quad
V=-\frac{2q_c}{3(q_c^2+q_c+1)},
\]
\[
W=HC\,R=
\frac{q_c(q_c+1)^2(q_c^2-q_c+1)}{9(q_c^2+q_c+1)^3},\quad
p=\frac{3Hq_c}{B(q_c^2-q_c+1)}.
\]

The degree-six rational map to \(\kappa\) has the full S3 deck group
generated by \(q_c\mapsto\zeta_3q_c\) and \(q_c\mapsto1/q_c\). Its
branch values are \(0,-27/4,\infty\), with indices \((3,2,2)\).
The whole cyclic traces satisfy \(\operatorname{Tr}V=\operatorname{Tr}W=0\)
and \(\operatorname{Tr}F=1\). The full physical \(H,B,C\) remain variable;
both \(F\) and \(W\) bind to their actual cubic-field source formulas.

This rational cover is compatible with the earlier fixed elliptic cover
\(Y^2=X^3-16\) over \(j\), where \(\kappa=j^3\). Explicitly, choose

\[
q_c=\frac{4\sqrt3-Y}{4\sqrt3+Y}.
\]

The audit checks its \(\kappa,F,W\) formulas exactly. Elliptic translation
by \((0,4i)\) becomes \(q_c\mapsto\zeta_3q_c\) with
\(\zeta_3=(-1+i\sqrt3)/2\), while \(Y\mapsto-Y\) becomes inversion.
The map \(X\mapsto\zeta_3X\), fixing \(Y\), is the cube-root-normalization
quotient. Thus the rational cover over \(\kappa\) and elliptic cover over
\(j\) are consistent; they are not being identified over different base
parameters without this finite normalization.

The independent standard-library checkers passed 27 normal/source checks
(`verify_fano_normals_fraction.py`) and 26 rational-cover/elliptic-bridge
checks (`verify_rational_kappa_fraction.py`). Results are saved beside them.
No differential primitive or jet-compatible companion theorem is asserted.
