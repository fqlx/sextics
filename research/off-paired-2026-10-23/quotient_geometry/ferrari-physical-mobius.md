# A physical lift of the Ferrari Möbius field

This is an exact source-preserving interface, not a primitive. The quartic
convention is \(G=v^4+Sv^2+Tv+R\), with \(R=u^6,T=eu^3\).

Put
\[
 p=ab,\quad e=zp/2,\quad f=z/2+p/3,\quad
 h=S-1-z^6-uf=a^6+b^6,\quad Z=b^6-a^6.
\]
The relative physical volume is
\[
 du\wedge dz\wedge da\wedge db
 =\frac{du\wedge dz\wedge de\wedge dS}{3zZ}.
\]
This includes the quadratic inverse-Jacobian branch density.

The coefficient Möbius field
\[
 M=3T\partial_S+(4R-S^2)\partial_T-\frac{ST}{2}\partial_R
\]
has the following rational lift holding \(z\) fixed:
\[
 U=M(u)=-\frac{Se}{12u^2},\qquad
 E=M(e)=\frac{4u^6-S^2+Se^2/4}{u^3},\qquad
 M(S)=3eu^3,
\]
\[
 P=M(p)=2E/z,\qquad G=M(h)=3eu^3-fU-uP/3,
\]
\[
 M(a)=\frac{6b^5P-aG}{6Z},\qquad
 M(b)=\frac{bG-6a^5P}{6Z}.
\]
Its physical divergence, relative to the displayed physical volume, is
\[
 \boxed{\operatorname{div}_{\rm phys}M
 =\frac{2Se}{3u^3}-\frac{hG-12p^5P}{Z^2}.}
\]
The first term is the divergence in \((u,z,e,S)\). The second is exactly
\(-M(\log Z)\). Thus the coefficient identity
\[
 M(q_S)=\frac{T}{q^2}q_S+2S q_T+\frac{T}{2}q_R
\]
becomes the exact physical current identity
\[
 \operatorname{div}_{\rm phys}(q_SM)
 =\left(\operatorname{div}_{\rm phys}M+\frac{T}{q^2}\right)q_S
   +2S q_T+\frac{T}{2}q_R.
\]
The extra \(Z^{-2}\) term is part of the original source problem. Dropping
it would replace the physical density by the coefficient density. This
lift can be combined with the Euler and angular current identities in
`../geometry/potential-current/ferrari-mobius-identities.md`; no such
combination giving the actual pair source has yet been found.

All source coefficients in the pair notes use their stated relative
residue convention. The ambient ordering \(du\wedge dv\wedge dz\wedge
 da\wedge db\) introduces the overall minus specified there.

Prepared with OpenAI Codex assistance.
