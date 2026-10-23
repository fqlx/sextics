# Audited Möbius identities for the Ferrari pair coordinate

The convention here is

\[
 G(v)=v^4+Sv^2+Tv+R,\quad R=u^6,\quad T=eu^3,
\]

so \(R\) is the constant coefficient and \(T\) the linear coefficient.
The pair sum \(q\) satisfies

\[
 P=q^6+2Sq^4+(S^2-4R)q^2-T^2=0.
\]

These are source-carrying algebraic identities, not a rational current.

## Full quadratic Möbius variation

The infinitesimal root transformation \(v\mapsto v+\epsilon v^2\), followed
by recentering to preserve the depressed quartic, induces

\[
 M=3T\partial_S+(4R-S^2)\partial_T-\frac{ST}{2}\partial_R.
\]

It has zero coefficient divergence. Its lift to the pair field obeys

\[
 M(q)=-T/q,\quad M(q^3)=-3Tq,\quad M(q^5)=-5Tq^3.
\]

In particular,

\[
 M^2(q)=-q^3-2Sq,\quad M^3(q)=-2S M(q)-3Tq.
\]

Differentiating the first identity with respect to \(S\) yields

\[
 3Tq_{SS}+(4R-S^2)q_{ST}-\frac{ST}{2}q_{SR}
 =\frac{T}{q^2}q_S+2S q_T+\frac T2 q_R.
\]

This is an actual relation among the highest derivatives occurring in a
current using \(q_S,q_R,q_T\). A physical lift must retain its own divergence
and the physical volume coefficient; coefficient divergence zero alone does
not establish physical divergence zero.

## Invariants and the physical lift

The invariants

\[
 I=S^2+12R,\quad J=72SR-27T^2-2S^3
\]

satisfy \(M(I)=M(J)=0\). At fixed \(I,J\),

\[
 T^2=(6IS-8S^3-J)/27,
\]

an elliptic coefficient orbit generically. The physical relation
\(R=u^6\) imposes

\[
 M(u)=-\frac{ST}{12u^5}.
\]

For generic \(I,J\), the function \(R=(I-S^2)/12\) has simple zeros on this
elliptic curve at \(S=\pm\sqrt I\) with \(T\ne0\). Adjoining the actual
physical \(u\) therefore gives a ramified cover. An étale pair-sign isogeny
stays étale after this base change, but the resulting higher-genus curve can
have nonzero anti-invariant first cohomology. Exactness of an odd
second-kind differential on the original elliptic orbit cannot simply be
transplanted to this physical cover.

An open constructive adjustment is the shifted Euler field

\[
 E_c=2S\partial_S+3T\partial_T+4R\partial_R,\qquad
 M'=M+\frac{ST}{8R}E_c.
\]

Then \(M'(R)=0\), so the physical \(u\) can be fixed, and
\(J^2/I^3\) remains invariant. This removes that particular root-ramification
mechanism; it does not establish an elliptic physical orbit, unramified
coefficient transport, a correct physical divergence, or a primitive. Those
remain explicit obligations.
