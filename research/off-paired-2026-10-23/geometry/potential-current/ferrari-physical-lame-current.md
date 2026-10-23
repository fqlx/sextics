# A physical Lamé concomitant retaining the branch density

This gives exact source-carrying current formulas, conditional on an explicit
inhomogeneous scalar solution. No such solution has been found here.

Use the coefficient convention \(G=v^4+Sv^2+Tv+R\), \(R=u^6,T=eu^3\),
and the audited physical lift \(M\) holding \(z\) fixed. Let
\(Z=b^6-a^6\). Its divergence is exactly

\[
 d=\operatorname{div}_{\rm phys}M
 =-8M(\log u)-M(\log Z).
\]

Hence

\[
 \mu=u^8Z,\qquad \operatorname{div}_{\rm phys}(\mu M)=0.
\]

This integrating factor includes the actual quadratic branch density.
Replacing it by a constant would alter the source.

For a selected invariant resolvent root
\(\lambda=q^2+2S/3\), the pair coordinate satisfies the second-order Lamé
identity

\[
 M^2q+\left(\frac{4S}{3}+\lambda\right)q=0.
\]

For any rational function \(r\) on the full physical pair cover, the
following is therefore an **exact physical divergence identity**:

\[
 \boxed{\operatorname{div}_{\rm phys}\!left[
 \mu\bigl(qM(r)-M(q)r\bigr)M\right]
 =\mu q\left[M^2r+\left(\frac{4S}{3}+\lambda\right)r\right].}
\]

If the desired actual pair source is written \(qf\), it suffices to
construct rational \(r\) satisfying

\[
 M^2r+\left(\frac{4S}{3}+\lambda\right)r=f/\mu.
\]

The factor \(1/\mu\) is the unresolved physical forcing. The universal
coefficient-orbit scalar integral does not remove it.

A corresponding third-order form uses \(D=M+d\):

\[
 J=qD^2r+\frac Tq Dr-q^3r,
\]

\[
 \boxed{\operatorname{div}_{\rm phys}(JM)
 =q\bigl(D^3r+2SDr+3Tr\bigr).}
\]

It follows from \(M^3q+2SMq+3Tq=0\), retaining the physical divergence in
every occurrence of \(D\). Neither formula by itself establishes a
primitive: an actual scalar solution and all descent/legal-denominator
conditions remain necessary.
