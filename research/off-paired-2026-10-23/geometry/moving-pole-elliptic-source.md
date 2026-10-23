# Source-carrying elliptic quotients for a moving endpoint pole

This is an exact constructive source calculation, not an endpoint elliptic-factor claim or a certificate.

The fixed affine base is

\[
 H=1+x^6+y^6+z^6+xyz/2,\quad
 C=x^3z/2+xy/3.
\]

Choose the moving endpoint coordinate \(p_0=-3z/2\). Then

\[
 H+Cp_0=y^6+K,\qquad
 K=1+x^6+z^6-3x^3z^2/4.
\]

The ordinate of a pole section lies on the companion

\[
 V_0^2=(y^6+K)^2-4p_0^6.
\]

The physical one-variable density is \(y^3dy\). Using \(s=y^2\), it is
\(s\,ds/2\). Thus its quotient companion is

\[
 V_0^2=s^6+2Ks^3+B,\qquad B=K^2-4p_0^6.
\]

Adjoin \(b\) with \(b^6=B\); this is a finite algebraic extension on the
nonzero generic open \(B\ne0\). Put

\[
 u=s/b,\quad v=V_0/b^3,\quad \alpha=2K/b^3.
\]

Then \(v^2=u^6+\alpha u^3+1\). The two involutions
\((u,v)\mapsto(1/u,\pm v/u^3)\) have genus-one quotients

\[
 X=u+u^{-1},\qquad Y_\pm=v(u\pm1)/u^2,
\]

\[
 E_\pm:\quad Y_\pm^2=(X\pm2)(X^3-3X+\alpha).
\]

Their differential pullbacks are

\[
 \frac{dX}{Y_+}=(u-1)\frac{du}{v},\qquad
 \frac{dX}{Y_-}=(u+1)\frac{du}{v}.
\]

Consequently the **actual physical density** obeys

\[
 \boxed{\frac{y^3dy}{V_0}
 =\frac1{4b}\left(\frac{dX}{Y_+}+\frac{dX}{Y_-}\right).}
\]

All these differential identities hold with \(x,z\) fixed. Coefficient
derivatives in \(x,z\) must retain variation of \(p_0,K,B,b,\alpha\), the
quotient maps, and the endpoint pole section. Their variation is not zero.

For example,

\[
 j(E_+)=-\frac{6912(2\alpha+5)^3}{(\alpha-2)^3(\alpha+2)}.
\]

Thus these elliptic curves vary with the physical base. The shared elliptic
contraction library is stated for the Fermat elliptic curve and cannot be
applied directly to these curves solely because they are elliptic.

The next source-carrying obligation is to differentiate an actual moving
third-kind endpoint kernel at this section and match its compact connection
terms to the original source, retaining residues and all coefficient-map
corrections. Splitting this companion does not split the original endpoint
Jacobian, which remains generically absolutely simple.

Prepared with OpenAI Codex assistance.
