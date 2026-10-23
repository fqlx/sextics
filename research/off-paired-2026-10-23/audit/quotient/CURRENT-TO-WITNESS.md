# Conditional endpoint-current to physical-witness algorithm

No current satisfying the source equation is supplied here. This gives explicit
finite algebraic steps for converting such a current into the exact six-field
certificate, including moving poles, nonzero residues, and exact Dwork terms.

## Input and conventions

Work first in the source-density quotient, with base coordinates
\(q=(u,v,z)\), \(\mu=du\wedge dv\wedge dz\), and

\[
H=1+u^6/v^2+v^2+z^6+uz/2,\quad
C=u^3z/(2v)+u/3,\quad
F_*=a^6+b^6+Cab+H.
\]

The actual five-form is
\(A_0\mu\wedge da\wedge db/F_*^2\), where \(A_0=1/3\). Put
\(p=ab\), \(Z=b^6-a^6\). On \(F_*=0\),
\(Z^2=f=(H+Cp)^2-4p^6\). The square-root sign is fixed here, not inferred
from the equation for \(Z^2\).

Allow the compact forms \(p^jdp/Z\), \(j=0,1,3,4\); the infinity
third-kind form \(p^2dp/Z\); and any finite set of distinct moving-pole forms
\(dp/((p-r_\ell)Z)\), with base-rational \(r_\ell\) and
\(f(r_\ell)\ne0\). Write all these representatives as
\(\omega_j=k_j(p)dp/Z\). Let \(R_{i,j}\) denote the **numerators** of the
exact Dwork terms:

\[
\partial_{q_i}\omega_j=\sum_k(B_i)_{kj}\omega_k
       +d_p(R_{i,j}/Z).
\]

For a moving pole, \(B_i\) and \(R_{i,j}\) include its derivative
\(\partial_{q_i}r_\ell\), not just \(H_i,C_i\). Thus

\[
R_{i,j}=H_iR_{H,j}+C_iR_{C,j}
             +\sum_\ell(r_\ell)_iR_{r_\ell,j}.
\]

The reconstructed JSON files contain these exact numerators. Some moving-pole
numerators are rational in \(p\), which is allowed.

The required input is a base-rational coefficient current \(a_{i,j}(q)\)
satisfying **every row** of

\[
\sum_i\left(\partial_{q_i}a_i+B_i a_i\right)
=-\frac{A_0}{6}M_He_0=-\frac1{18}M_He_0.
\]

In particular, the infinity-residue row requires ordinary divergence zero, and
each moving finite-pole row requires its twisted divergence zero. These rows
cannot be discarded because the source has zero residues. They do not require
each residue-current coefficient to vanish separately.

## Restore the exact terms before lifting

Define

\[
h_i(p)=\sum_j a_{i,j}k_j(p),\qquad
T(p)=\sum_{i,j}a_{i,j}R_{i,j}(p)+\frac{A_0}{6}R_{H,0}(p).
\]

Then the rational three-form on the fourfold \(F_*=0\)

\[
\eta=\sum_i(\iota_{\partial_{q_i}}\mu)\wedge h_i(p)\frac{dp}{Z}
                 +\mu\frac{T(p)}Z
\]

satisfies the literal differential identity

\[
d\eta=-\frac{A_0}{6}\mu\wedge\partial_H(dp/Z).
\]

Indeed the Dwork exact terms from the base current sum to
\(d_p(\sum aR/Z)\). The extra \(\mu T/Z\) contributes
\(-\mu\wedge d_p(T/Z)\), cancelling those terms and supplying the exact
part \(-A_0d_p(R_{H,0}/Z)/6\) of the source. A cohomology-vector identity
alone is not the literal primitive until this correction is included.

## Explicit rational ambient field

Use the normal coordinate \(t=F_*\) while fixing \(q,p\). Then

\[
Z_t^2=(H-t+Cp)^2-4p^6,\qquad
\Omega=\mu\wedge da\wedge db
       =\frac{dt\wedge\mu\wedge dp}{6Z_t}.
\]

Extend all Dwork numerators by replacing their independent \(H\) argument by
\(H-t\). The base coefficients \(a_{i,j}(q)\), \(H_i,C_i,(r_\ell)_i\)
remain fixed base functions. The representatives \(k_j(p)\) remain as above.
Let \(\widetilde T\) be the resulting extension of \(T\), and put

\[
P=6\widetilde T
  =6\sum_{i,j}a_{i,j}\widetilde R_{i,j}
       +A_0\widetilde R_{H,0},
\qquad
L=A_0+6\sum_i h_i(H_i+C_ip).
\]

The required ambient field has base components and endpoint components

\[
V_{q_i}=-6h_i,\qquad
V_a=\frac{(F_*)_bP-aL}{6Z},\qquad
V_b=\frac{bL-(F_*)_aP}{6Z}.
\]

Here \(t=F_*\) and \(Z=b^6-a^6\) are substituted at the end. Exact
algebra gives

\[
V(F_*)=A_0,\qquad V(p)=P.
\]

The normal-coordinate identity behind this formula is

\[
\iota_V\Omega=\beta(t)+dt\wedge\eta(t),\qquad
\beta(t)=\frac{A_0}{6}\mu\wedge\frac{dp}{Z_t}.
\]

Since
\(\partial_t\beta(0)=-A_0\mu\wedge\partial_H(dp/Z)/6=d\eta(0)\),

\[
d\left(\frac{\iota_V\Omega}{t}\right)
=-\frac{A_0\Omega}{t^2}
 +\frac{dt}{t}\wedge\left(\partial_t\beta-d\eta\right).
\]

The final term is regular at the generic point of \(t=0\). Thus
\(\operatorname{div}V\) is divisible by \(F_*\) in the localization away
from \(F_*\), and the complete non-strict certificate equation follows.
The sign uses \(Z=b^6-a^6\) and the normal differential placed first.

`verify_current_lift_fraction.py` independently checks the two displayed field
equations and the exact algebraic relation between literal residue error and
normal divergence. The compact, infinity, and moving-pole Dwork identities have
separate exact verifiers. No actual source current is established by these
conditional calculations.

## Return to the original variables

Because this field uses \(F_*\), not the cleared equation \(G=v^2F_*\),
its direct pullback is especially simple. With all quotient fields evaluated at
\(u=xy,v=y^3\), put

\[
\begin{aligned}
V_x^{\rm phys}&=3y^2V_u-xV_v,&
V_y^{\rm phys}&=yV_v,\\
V_z^{\rm phys}&=3y^3V_z,&
V_a^{\rm phys}&=3y^3V_a,&
V_b^{\rm phys}&=3y^3V_b.
\end{aligned}
\]

This is the ordinary Piola field \(J(d\theta)^{-1}V\), with \(J=3y^3\).
It has the exact source \(J A_0=y^3\) and retains any remainder. Equivalently
one may first use \(W=v^2V\) for \(G\), then apply `TRANSPORT.md`; both
give the same physical field.

Homogenize this rational physical field by
\(V_i^h=X_0V_i^{\rm phys}(X_1/X_0,Y_0/X_0,Y_1/X_0,X_2/X_0,Y_2/X_0)\)
and insert \(V_0=0\). The six components are ordered
\((0,V_x^h,V_a^h,V_y^h,V_z^h,V_b^h)\). The source becomes exactly
\(X_0^3Y_0^3\). If homogeneous quotient data are used directly, their source
is \(A_0^h=X_0^3/3\), not the constant \(1/3\).

## Denominators and final finite checks

Base-rational coefficients introduce only base denominators, which are coprime
to the physical sextic by monicity in \(X_2\). The endpoint denominator
\(Z=b^6-a^6\) has linear factors \(b-\zeta a\), \(\zeta^6=1\); no such
factor divides \(F_*\), whose restriction has a nonzero leading sextic term.
The moving-pole denominator \(ab-r\) is coprime to \(F_*\): substituting
\(a=r/b\) leaves a nonzero Laurent polynomial with leading \(b^6\) term.
For \(r=0\), neither \(a\) nor \(b\) divides \(F_*\).

Normal-extension denominators such as \(L(H-F_*,C)\) reduce modulo \(F_*\)
to the nonzero base polynomial \(L(H,C)\). Any common factor would therefore
divide both \(F_*\) and a nonzero base polynomial, which is impossible.
The same argument applies to \(f(r;H-F_*,C)\), provided the supplied pole
stays generically off the branch divisor. Homogenization may introduce an
\(X_0\)-factor; that factor is legal since \(F|_{X_0=0}\ne0\).

Clear all denominators to a nonzero homogeneous polynomial \(D\) and form
\(N_i=DV_i^h\). Then \(\deg N_i=\deg D+1\), and
\(\sum_iN_iF_i=AD\) holds exactly. Compute, by exact polynomial division,

\[
Q=\frac{D\sum_i\partial_iN_i-\sum_iN_i\partial_iD}{F}.
\]

The full cohomological construction predicts this quotient is polynomial; an
actual candidate must pass this exact division and the complete cleared identity
independently. Then verify nonvanishing, homogeneous degrees, and complex
coprimality for the exact exported \(D,N,Q\). A failed division is a failed
candidate or transport computation, not something to drop as a remainder.

The finite-pole forms are rational differentials of third kind; no logarithm is
required. Literal logarithmic functions are not polynomial witnesses. If a
normalized-pole or geometric construction first uses a finite algebraic base
extension, average the assembled field by its normalized field trace only after
proving derivations commute with that trace and checking denominator norms.
The source is fixed by trace; its correction terms must be traced too.

Only after these exact candidate checks should the required Lean witness,
kernel verification, protected CI, and acceptance workflow begin.
