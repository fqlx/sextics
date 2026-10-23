# Complete Poisson-current interface and witness signs

No bracket decomposition of the fixed source is supplied. This establishes
precisely what an eventual decomposition would have to prove and how it would
produce the physical certificate.

Work over the constant field \(k=\mathbb C\) for the unrestricted contract;
the matrices and all displayed identities are defined over \(\mathbb Q\).
Use
\[
q=(z,U,K,t),\quad H=1+z^2+t,
\quad B=U/2+K/3+zUK/2,
\quad C=z^{-2}+U^6+K^6/t,
\]
\[
f=H+Bp+Cp^3,\quad g=3Cp^2+B,\quad
L=k(q)[p]/(f),\quad R=Bp/g^3.
\]
The actual physical residue is \(R\Omega\), where
\[
\omega=\frac{dz\wedge dU}{3z^2}+\frac{dK\wedge dt}{6t},
\qquad \Omega=\omega^2/2=\rho\,dz\wedge dU\wedge dK\wedge dt,
\quad\rho=\frac1{18tz^2}.
\]
The normal differential is placed first; moving \(dp\) past all four base
differentials has positive sign.

## Algebraic extension of the Poisson structure

The finite separable field extension has commuting coordinate derivations
\[
D_i(p)=-\frac{H_i+pB_i+p^3C_i}{g}.
\]
They commute because their commutator is a derivation zero on the base field,
and such a derivation is zero on a separable algebraic extension.
The pullback of \(\omega\) remains closed and nondegenerate over \(L\).
It therefore defines the unique extended Poisson bracket
\[
\{F,G\}=3z^2(D_zF\,D_UG-D_UF\,D_zG)
 +6t(D_KF\,D_tG-D_tF\,D_KG).
\]

The convention is \(X_F(G)=\{F,G\}\), so
\(\iota_{X_F}\omega=-dF\). This sign gives
\(\mathcal L_{X_F}\omega=0\), hence
\(\operatorname{div}_\Omega X_F=0\), for every \(F\in L\), not just
base-rational Hamiltonians. Equivalently, the coordinate proof uses only the
commuting \(D_i\) and the exact scalar density \(\rho\).

For any \(a,F\in L\),
\[
d(a\,\iota_{X_F}\Omega)=\{F,a\}\Omega.
\]
Thus an exact identity \(R=\sum_j\{F_j,a_j\}\) would provide the rational
three-form primitive
\[
\eta=\sum_ja_j\iota_{X_{F_j}}\Omega
     =-\sum_ja_j\,dF_j\wedge\omega.
\]
All functions and differentials here are algebraic/rational; literal
logarithmic functions are not introduced.

## Four base Hamiltonians already give every current

On \(zt\ne0\), the coordinate Hamiltonians form the complete rational frame
\[
X_z=3z^2D_U,\quad X_U=-3z^2D_z,
\quad X_K=6tD_t,\quad X_t=-6tD_K.
\]
Every \(L\)-valued base current \(A=\sum_i a_iD_i\) has the unique form
\[
A=b_zX_z+b_UX_U+b_KX_K+b_tX_t,
\]
where
\[
b_z=\frac{a_U}{3z^2},\quad b_U=-\frac{a_z}{3z^2},
\quad b_K=\frac{a_t}{6t},\quad b_t=-\frac{a_K}{6t}.
\]
Consequently the unrestricted rational-current equation is exactly
\[
\boxed{\{z,b_z\}+\{U,b_U\}+\{K,b_K\}+\{t,b_t\}=R.}
\]
This is a complete reformulation, not a new sufficient subspace. Restricting
the denominators, numerator degrees, coefficient functions, or number of
nonzero terms would create a restricted search ansatz.

Because these four Hamiltonians lie in the base field, their derivations
commute with the field trace. Since \(\operatorname{Tr}R=0\), the four
coefficients can be projected to trace zero. Each can therefore be written
uniquely as
\[
b_j=b_{j1}p+b_{j2}\left(p^2+\frac{2B}{3C}\right),
\quad b_{jk}\in k(z,U,K,t).
\]
For coefficient columns in this basis, the complete equation is
\[
3z^2(\partial_Ub_z+M_Ub_z)
-3z^2(\partial_zb_U+M_zb_U)
+6t(\partial_tb_K+M_tb_K)
-6t(\partial_Kb_t+M_Kb_t)=r,
\]
where \(M_i=H_iM_H+B_iM_B+C_iM_C\) and \(r\) is the audited two-entry
source column. The matrix convention is derivative-of-basis columns.

Trace zero alone does not prove that this equation has a rational solution.
Likewise, finding a rational Darboux pair \(\{r_0,U\}=1\) does not integrate
an arbitrary rational source: rational differentiation has residue obstructions.
An actual bracket identity or current is still required. For nonbase
Hamiltonians, the trace of a product cannot be replaced by a product of traces;
one should first assemble the complete current, then apply trace if needed.

## Verified coefficient-potential identities

The universal coefficient direction, before physical pullback, satisfies
\[
p_B=-p/g,\qquad p_{BB}=2Bp/g^3=2R,
\qquad \partial_B(-p/(2g))=R.
\]
This derivative holds at fixed \(H,C\). It is not the physical derivative
along a base coordinate unless a compatible physical lift is supplied.

The fully extended physical bracket instead gives
\[
\{p,p_B\}=-\frac{p}{g^3}
 \left(\{H,B\}+3p^2\{H,C\}+2p^3\{B,C\}\right),
\]
including all three coefficient variations. In particular,
\(\{H,C\}=36(z^3U^5-K^5)\), which is not zero. These identities retain the
actual source but do not on their own cancel its additional coefficient terms.

`verify_poisson_fraction.py` independently checks 49 exact polynomial/Laurent
identities: both coefficient-potential identities, all three terms of the last
bracket, the exact symplectic volume, arbitrary Hamiltonian divergence
coefficients, the coordinate frame and inverse, and the physical \(\{H,C\}\).

## Conditional ambient lift with all signs fixed

Given actual \(b_z,b_U,b_K,b_t\in L\) satisfying the boxed equation, form
the ordinary current components
\[
(a_z,a_U,a_K,a_t)
=(-3z^2b_U,\,3z^2b_z,\,-6tb_t,\,6tb_K).
\]
Then
\[
\sum_i\left(D_ia_i+(\partial_i\log\rho)a_i\right)=R,
\qquad \partial\log\rho=(-2/z,0,0,-1/t).
\]
Choose rational ambient representatives in \(q,p\), with denominators
nonzero modulo \(f\). With partial derivatives \(f_i\) taken at fixed
\(p\), set
\[
\mathcal V_{q_i}=-\rho g a_i,\qquad
\mathcal V_p=\rho\left(\frac{p^2}{2g}+\sum_i f_i a_i\right).
\]
Direct product differentiation gives
\[
\mathcal V(f)=\rho p^2/2,
\]
\[
\operatorname{div}\mathcal V
=\rho g\left[R-\sum_i\left(D_ia_i+
             (\partial_i\log\rho)a_i\right)\right]=0\pmod f.
\]
The \(g\)-derivative is included; it is what changes the raw second-normal
source to \(Bp/g^3\). These formulas use the field representatives directly,
so no compact-cohomology or moving-pole Dwork correction is being omitted.

Use the physical map
\[
z=x^3,\quad U=Y_1/(xy),\quad K=aY_2/(xy),
\quad t=a^6,\quad p=x^2y^2,
\]
whose signed Jacobian is \(J=36a^6x^2/y\). The physical field is
\[
W=J(d\theta)^{-1}\theta^*\mathcal V.
\]
The exact source identity is
\(J\theta^*(\rho p^2/2)=y^3\), so
\(W(F)=y^3\) and \(\operatorname{div}W=0\pmod F\). The required
certificate sign is consequently
\[
A-W(F)+F\operatorname{div}W=0\pmod{F^2}.
\]
There is no extra minus sign between the boxed bracket equation and the
physical source.

Homogenize \(W\) with zero \(X_0\) component, clear a nonzero homogeneous
denominator \(D\), and put \(N_i=DW_i\) in the immutable variable order.
The exact finite output must satisfy
\[
N(F)=AD,\qquad
Q=\frac{D\operatorname{div}N-N(D)}F\in\mathbb C[X_0,\ldots,Y_2].
\]
Then the full cleared certificate identity has remainder \(F^2Q\).
Nonvanishing, homogeneous degrees and complex coprimality must be checked for
those exact exported polynomials. The generic field condition on denominators
and the irreducible physical target permit legal clearing; it is not a substitute
for checking the final candidate. Protected Lean/kernel verification and CI
remain separate subsequent obligations.
