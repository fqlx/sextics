# A smooth bundle resolution of the cubic support D3

This audits the proposed support \(D_3:3X_1^2Y_1+2X_0^2Y_0=0\).
It does not give a certificate. The result concerns this divisor only.

Let
\[
 T=\mathbf P_{\mathbf P^1}\bigl(\mathcal O(-1)\oplus
 \mathcal O(-2)\oplus\mathcal O\oplus\mathcal O\bigr),
\]
using lines in the vector bundle. In base coordinates \((r:s)\), write
fiber coordinates \((\lambda,\mu,a,b)\), and map to \(\mathbf P^5\) by
\[
 X_0=r\lambda,\quad X_1=s\lambda,\quad X_2=a,\quad
 Y_0=3s^2\mu,\quad Y_1=-2r^2\mu,\quad Y_2=b.
\]
These six sections have no common zero. The map is birational onto the
binomial ambient hypersurface. Its restriction gives a proper birational
map \(Z_3\longrightarrow X\cap D_3\), where
\[
 Z_3:\ a^6+b^6+(r^6+s^6)\lambda^6
 +(729s^{12}+64r^{12})\mu^6
 -3r^5s^3\lambda^4\mu^2=0.
\]
In particular, the two mixed terms involving \(ab\) cancel exactly.

## Smoothness and the global H20

The partial derivatives in \(a,b\) show that any singular point would
have \(a=b=0\). Thus smoothness reduces to the binary sextic in
\(\lambda,\mu\). On \(s=1\), put
\[
 A=q^6+1,\quad D=-3q^5,\quad B=729+64q^{12},
\]
\[
 C=A^2B-4q^{15}.
\]
The cubic in \(L=\lambda^2,M=\mu^2\) has discriminant
\(-27BC\). The polynomials \(A,B,C\) are squarefree and pairwise
coprime; these are exact rational polynomial gcd checks. The double
roots of the cubic are therefore transverse in the base direction.
The charts at \(q=0,\infty\) have diagonal smooth sextic fibers. These
facts prove that the total threefold \(Z_3\) is smooth.

Let \(H=\mathcal O_T(1)\) and \(E=\mathcal O(-1)\oplus
\mathcal O(-2)\oplus\mathcal O^2\). The equation has class \(6H\).
The exact sequence
\(0\to\mathcal O_T(-6H)\to\mathcal O_T\to\mathcal O_{Z_3}\to0\)
and relative Serre duality give
\[
 H^2(Z_3,\mathcal O_{Z_3})
 =H^0\!\left(\mathbf P^1,
 [\operatorname{Sym}^2E^*\otimes\mathcal O(3)]^*\right)=0.
\]
Every summand in the displayed bundle has degree between \(-7\) and
\(-3\). Hence this smooth resolution has \(H^{2,0}=0\). In particular,
this proposed divisor alone has no \(H^{2,0}\) cylinder that can carry the
nonzero invariant \(H^{3,1}\) source, regardless of pole order.

## Why the fiber K3 observation is insufficient

Fiberwise quotienting by the two independent signs of \(\lambda,\mu\)
gives the weighted K3 equation
\[
 a^6+b^6+A L^3+D L^2M+B M^3=0
 \quad\text{in }\mathbf P(1,1,2,2).
\]
A binary cubic can be normalized after a finite base extension, so this
K3 sector is isotrivial there. Its holomorphic two-form pulls back with
numerator \(\lambda\mu\). Global Y sign sends
\((\mu,b)\mapsto(-\mu,-b)\), so this particular two-form is odd. Its
finite base monodromy also prevents a global holomorphic two-form on
\(Z_3\), consistently with the bundle calculation.

When using the full-G36 surface model, replacing \(K\) by
\(L=pK^2\) is an additional quotient: the full field also retains
\(r=pK\) with \(r^2=pL\). The rational elliptic quotient obtained after
forgetting that square root does not compute the H20 of the full fiber.
The global bundle calculation above avoids this field-drop issue.

Prepared with OpenAI Codex assistance.
