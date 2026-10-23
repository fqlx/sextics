# Physical Hamiltonian currents and the original witness

This note gives an actual physical first current, its precise correction,
and a conditional lift of any completed Poisson construction. No complete
current or certificate has been found.

## Physical bracket and a first current

Use the full diagonal quotient in `../cubic-ray/INTERFACE.md`:
\[
 f=H+Bp+Cp^3,\quad g=f_p=3Cp^2+B,\quad
 \Omega=\rho\,dz\wedge dU\wedge dK\wedge dt,\quad
 \rho=1/(18tz^2),\quad R=Bp/g^3.
\]
The closed rational symplectic form
\[
 \omega=\frac{dz\wedge dU}{3z^2}+\frac{dK\wedge dt}{6t}
\]
has \(\omega^2/2=\Omega\). Define
\[
 \{F,G\}=3z^2(D_zF D_UG-D_UF D_zG)
       +6t(D_KF D_tG-D_tF D_KG),
\]
where \(D_i=\partial_i-(f_i/g)\partial_p\) on the cubic field. This note
uses the **right Hamiltonian convention**
\(X_G^i=\pi^{ij}D_jG\), so \(X_G(F)=\{F,G\}\) and
\(\iota_{X_G}\omega=dG\). The exact identity
\(\operatorname{div}_{\rho}X_G=0\) holds for every rational \(G\) in this
field. Hence
\[
 \operatorname{div}_{\rho}(F X_G)=\{F,G\}.
\]
A rational logarithmic differential may also define \(X_G\): for example
\(G=\log t\) is shorthand for using \(dG=dt/t\); no logarithm need
appear in the resulting current.

All three coefficient brackets are physical:
\[
 A=\{H,C\}=36(z^3U^5-K^5),
\]
\[
 D=\{B,C\}=9z^2U^6K+3(1+zK)/z-(2+3zU)K^6/t,
\]
\[
 E=\{H,B\}=3z^3+3z^4K-2t-3tzU.
\]
Put
\[
 Q=3p^2A+2p^3D+E,\qquad A_0=Bp/Q.
\]
Then \(\{p,g\}=-Q/g\). Define \(N\) by its components, with \(p\)
held constant when taking base partial derivatives:
\[
 N=(3z^2f_U,-3z^2f_z,6tf_t,-6tf_K),\quad N(p)=0.
\]
Thus \(N=X_f\) for the right convention used here. For the alternative
left convention \(X_F(G)=\{F,G\}\), it is \(-X_f\). The actual
components do not change. On the cubic cover,
\(\iota_N\omega=-g\,dp\).
It satisfies
\[
 \{p,F\}=N(F)/g,\quad N(g)=-Q,\quad
 \operatorname{div}_{\rho}N=-Q/g
\]
in the cubic field. The last divergence includes the implicit derivative
of \(p\); its omission would change the current identity.

The **actual physical first current**
\[
 \boxed{a^i=\frac{Bp}{Qg^2}N^i=-\frac{Bp}{Qg}X_p^i}
\]
satisfies
\[
 \boxed{\operatorname{div}_{\rho}a
 =R+\frac{N(Bp/Q)}{g^2}.}
\]
Equivalently,
\[
 R=\{p,Bp/(Qg)\}-N(Bp/Q)/g^2.
\]
The correction has pole order at most two in \(g\) at generic points of
\(g=0\), whereas the original source has order three. All derivatives
in \(N(Bp/Q)\) hold \(p\) constant; the new denominator \(Q\) is
retained. Constructing a current for the negative of this correction, or
another finite combination of explicit brackets yielding \(R\), is open.

For this first current, \(\sum_i f_i a^i=0\). Its ambient vector in the
construction below therefore simplifies to
\[
 V_i=-\frac{\rho Bp}{Qg}N^i,\qquad
 V_p=\frac{\rho p^2}{2g}.
\]
It already carries the exact numerator:
\[
 V(f)=\rho p^2/2,\qquad
 \operatorname{div}V=-\frac{\rho}{g}N(Bp/Q).
\]
The displayed divergence is a genuine remaining correction, not zero
modulo \(f\). For example, at \((z,U,K,t)=(1,1,1,2)\), the numerator
\(N(B)Q-BN(Q)\) reduces modulo \(f\) to
\(16(497677p^2-89652p-216684)/225\).

## From a completed sum of brackets to the original witness

There is also a simpler sufficient current ansatz that uses every physical
base direction without requiring a divergence-free lift. Put
\(\Delta=4B^3+27CH^2\). In the cubic field,
\[
 \Delta=g^2(g+3B),\qquad
 R=\frac{B^2p-3BH}{g\Delta}.
\]
Let \(V\) be a rational vector field on the physical base and let
\(d=\operatorname{div}_{\rho}V\). Then the current \(a=pV\) serves the
entire source precisely when
\[
 \boxed{V(H)-\frac HC V(C)+3Hd=\frac{3BH}{\Delta},\qquad
 V(B)-\frac BC V(C)+2Bd=-\frac{B^2}{\Delta}.}
\]
Indeed, the general formula is
\[
 \operatorname{div}_{\rho}(pV)=\frac{
 -V(H)+(H/C)V(C)-3Hd
 +p[-V(B)+(B/C)V(C)-2Bd]}{g}.
\]
The two boxed conditions allow \(V(C)\) and the physical divergence to
vary. They are broader than a divergence-free lift of a prescribed
coefficient vector. They are still a sufficient ansatz: a general
trace-free current has two independent cubic components. No rational
\(V\) satisfying the conditions has been constructed here.

Suppose an actual rational identity in the cubic field is obtained:
\[
 R=\sum_\alpha\{F_\alpha,G_\alpha\}.
\]
Set \(a^i=\sum_\alpha F_\alpha X_{G_\alpha}^i\), and choose rational
ambient representatives whose denominators are nonzero modulo \(f\).
Then \(\sum_iD_i(\rho a^i)=\rho R\). Define the ambient five-vector,
in coordinate order \((z,U,K,t,p)\), by
\[
 V_i=-\rho g a^i\quad(i=z,U,K,t),\qquad
 V_p=\rho\left[\frac{p^2}{2g}+\sum_i f_i a^i\right].
\]
It satisfies exactly \(V(f)=\rho p^2/2\), and
\(\operatorname{div}V=0\pmod f\).

Return to original affine variables
\[
 x=X_1,\quad a=X_2,\quad y=Y_0,\quad
 z=x^3,\ U=Y_1/(xy),\ K=aY_2/(xy),\ t=a^6,\ p=x^2y^2.
\]
The coordinate Jacobian is \(J=36tx^2/y\). Its Piola pullback is the
following original-coordinate rational vector field:
\[
 W_{X_1}=12tV_z/y,\qquad W_{X_2}=6ax^2V_t/y,
\]
\[
 W_{Y_0}=18tV_p/y^2-12tV_z/x,
\]
\[
 W_{Y_1}=36tx^3V_U+18tY_1V_p/y^3,
\]
\[
 W_{Y_2}=36tx^3V_K/a
       +Y_2(18tV_p/y^3-6x^2V_t/y).
\]
Thus \(W(F)=J\rho p^2/2=y^3\) and
\(\operatorname{div}W=0\pmod F\). Clearing a common denominator and
homogenizing gives the original-target polynomial identity described in
`../cubic-ray/INTERFACE.md`. Complex coprimality, exact clearing, and the
Lean submission workflow remain necessary after a completed current.

Prepared with OpenAI Codex assistance.
