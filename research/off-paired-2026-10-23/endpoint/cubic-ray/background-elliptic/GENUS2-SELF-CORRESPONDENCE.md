# Same-family genus-two graph and the complete moving-point kernel

This is an explicit correction kernel for the actual two-family source
problem. It is not a primitive of that source. In particular, its exact
meromorphic differential must not be identified with a nonzero proper
holomorphic two-form residue.

Fix a characteristic-zero constant field k; use k=C for the full contract.
The background third quotient has

    w^2=(D+Bq)^2-4q^6,
    D=H-1-z^6, B=-z/2.

The endpoint is Zp^2=(H+Cp)^2-4p^6 with its complete physical
C=q/3+z(s+d)/4. The genus-two modulus here is C^3/H^2; it is not the
kappa used in the separate cubic-ray rank-two connection.

## Actual isomorphism branch and all scale terms

One isomorphism branch is

    G=8D^2 C^3+z^3 H^2=0.

Generically its scale is already rational on this graph:

    r=H*B/(D*C), r^3=H/D, r^2=C/B.

For the full curve isomorphism put p=rP, Zp=r^3 Y(P), where
Y(P)^2=(D+BP)^2-4P^6. Its relative and horizontal parts are

    omega_j(endpoint)
      =r^(j-2)*P^j dP/Y(P)+r^(j-3)*P^(j+1)dr/Y(P).

All five indices j=0,1,2,3,4 are retained. In particular

    omega2(endpoint)=Omega2(P)+[P^3/Y(P)]dlogr.

There are two independent points in the kernel below: P is the endpoint
point and q is the actual background point. The function P^3/Y(P) equals
the background Euler primitive q^3/w(q) only on the kernel diagonal P=q.

The involution (D,B)->(-D,-B) leaves the background sextic unchanged.
Consequently there is also the opposite-sign isomorphism branch
8D^2 C^3-z^3 H^2=0. The selected degree-24 branch above is valid; it is not
the full union of obvious branches.

Homogeneously, with t=X0, the selected denominator is

    8D6^2 C4^3+t^9 z^3 H6^2,
    H6=t^6+x^6+y^6+z^6+xyz*t^3/2,
    D6=H6-t^6-z^6, C4=t^2xy/3+x^3z/2.

It has degree twenty-four and is nonzero. Since it is independent of the
endpoint variables and F is monic in endpoint X2, it is complex-coprime to
F. This only validates a possible support. The independent graph check is
`../../../audit/rank4-relative/TWO-FAMILY-GRAPH-INTERFACE.md`.

The physical graph derivatives are not computed holding C constant. With
the actual C_H,C_q,C_z from `ACTUAL-PRYM-CURRENT.md`,

    G_H=16D C^3+24D^2 C^2 C_H+2z^3H,
    G_q=24D^2 C^2 C_q,
    G_z=-96D z^5 C^3+24D^2 C^2 C_z+3z^2H^2.

On G=0 use dq=-(G_H/G_q)dH-(G_z/G_q)dz, and

    dlogr=dH/H+dz/z-(dH-6z^5dz)/D
             -(C_H dH+C_q dq+C_z dz)/C.

These terms are required in every absolute graph pullback.

## Full rational moving-point kernel

On the product of the identical genus-two curves define the rational
one-form

    tau=w*dP/[(P-q)Y(P)].

Its residues at the two points above P=q are +1 and -1. Its full absolute
differential d tau is a globally defined closed, exact meromorphic
two-form. The separate relative pieces are not asserted to extend by
themselves as closed holomorphic forms.

Use omega_j(P)=P^j dP/Y(P), j=0,1,3,4. Let m_D be the first D column
of the exact universal rank-four connection, with fiber primitive
R_D(P)/Y(P), stored in `../../reconstructed-connection.json` after
(H,C,p)=(D,B,P). Write f(q)=(D+Bq)^2-4q^6 and

    v(q)=(8q^4,4q^3,-4q,-8), L=3D+2Bq.

All three actual parameter derivatives have compact projections and exact
fiber terms:

    partial_q tau = sum_j v_j(q)*omega_j(P)/w
                     +d_P[-Y(P)/(w(P-q))],

    partial_D tau = sum_j A_D,j(q)*omega_j(P)/w
                     +d_P[a_D(P,q)/(wY(P))],

    partial_B tau = sum_j A_B,j(q)*omega_j(P)/w
                     +d_P[a_B(P,q)/(wY(P))],

    A_D=-(2B*f(q)*m_D+q*v(q))/L,
    A_B=q*A_D+f(q)*m_D,
    a_D=-[(P*f(q)-q*f(P))/(P-q)+2B*f(q)*R_D(P)]/L,
    a_B=q*a_D+f(q)*R_D(P).

These are literal differential identities, not just matrix projections.
The apparent L poles cancel from the compact columns. The verifier exports
their explicit polynomial q numerators and exact fiber primitives. The
q-polynomials include the background q^2 infinity component; it has not
been omitted.

That infinity component has an exact paired normalization. The polynomial
q^2 coefficient in A_D is 4*M_D*e3, and in A_B it is
4*M_B*e3=4*M_D*e4. Consequently the rational two-form

    Khat=tau^dq-4*omega3(P)^Omega2(q)

has zero residues at both background infinities. Its full derivative is

    dKhat=d(tau)^dq-4*d(omega3(P))^Omega2(q)
                         +4*omega3(P)^d(Omega2(q)).

The q^2 row cancels; the last background derivative term remains, with all
four compact components and its exact fiber primitive. This supplies a
finite paired rank-five correction rather than discarding an infinity
row. It does not solve the physical source. The cancellation also holds
literally at infinity: if w~epsilon*q^3, epsilon^2=-4, the dq/q
coefficient of tau is -epsilon*omega3(P), while that of
4*omega3(P)^Omega2(q) is 4*omega3(P)/epsilon; they agree.

The derivation uses two exact identities

    partial_B tau-q*partial_D tau=w*partial_D omega0(P),
    (3D partial_D+2B partial_B+q partial_q)tau
      =-d_P[P*w/((P-q)Y(P))].

For the physical H,z change, use

    partial_H=partial_D,
    partial_z=-6z^5 partial_D-partial_B/2,

and then include every q_H,q_z and graph-scale term above. For example,
the full endpoint moving-pole one-form pulls back as

    tau_endpoint=tau+[P*w/((P-q)Y(P))]dlogr

when its moving pole is p=rq. This records the horizontal part explicitly.

## Klein bidifferential and its exterior sign

The symmetric polar is particularly small:

    F2(P,q)=2D^2+2DB(P+q)+2B^2Pq-8P^3q^3.

Let

    K=(Y(P)+w)dP/[2Y(P)(P-q)],
    Berg=(F2+2Y(P)w)dP*dq/[4(P-q)^2Y(P)w].

As a bidifferential coefficient identity,

    Berg=partial_q(K_P)*dP*dq
           -2omega1(P)Omega3(q)-4omega0(P)Omega4(q).

The q part of the exterior derivative d(K_P dP), in the ordered frame
dP wedge dq, is NEGATIVE partial_q(K_P) dP wedge dq. This sign must be
included when using the bidifferential identity as a current. The exact
fiber primitives above keep the remaining compact components and all
parameter derivatives.

## What remains

This kernel supplies a literal finite correspondence and a complete
normal-function extension on the identical-curve graph. It does not match
the physical forcing merely because the curves are isomorphic. The genus-two
modulus varies and has nontrivial Gauss-Manin monodromy. A nonexact closed
holomorphic/base residue, or a direct complete rational current, must still
carry the actual endpoint/background source. In particular the exact form
d tau alone cannot provide a nonzero proper H20 class after localization.

The actual mixed source being corrected is in `ACTUAL-PRYM-CURRENT.md` and
the complete five-row reduction is in
`../../../coupled-fresh/rank4-relative/two-operator/elliptic/TWO-FAMILY-SOURCE-OPERATOR.md`.
The complementary source-guided infinity Euler current is stored in
`infinity_euler_transfer.py`; it retains all endpoint-derivative defects
and makes no full source-closure claim.

`genus2_self_kernel.py` verifies the graph, all literal parameter columns,
moving-point primitive, complete kernel Euler identity, Klein polar and
bidifferential identity. No bounded denominator search or new exclusion
has been used here. No certificate has been found.
