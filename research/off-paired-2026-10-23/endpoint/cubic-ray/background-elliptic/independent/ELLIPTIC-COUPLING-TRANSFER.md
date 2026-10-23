# A source-guided transfer into the background genus-two quotient

The actual source admits the explicit H/q partial current below. Its
remaining correction is retained. Products created by differentiating the
endpoint coefficient C descend to the background genus-two quotient, whose
family has the same equation type as the compact endpoint family.
Neither a primitive nor a correspondence between their Jacobians is
established here.

Work over a fixed characteristic-zero field k; take k=C for the full
certificate contract. Use the exact source conventions in
`coupled-fresh/infinity-horizontal/BACKGROUND-ELLIPTIC-SOURCE.md`:

    K0=1+z^6-H,
    s^2=2q^3-zq/2-K0, d^2=-2q^3-zq/2-K0,
    C=q/3+z(s+d)/4,
    mu=1/d-1/s, nu=1/d+1/s, w=sd.

The source compact column is

    S=-(mu/72)*(nabla_H|C omega0)*dH^dq^dz,
    omega0=dp/Z, Z^2=(H+Cp)^2-4p^6.

## Physical coupling derivatives

All derivatives here act on the actual physical field. In particular
K0_H=-1 and K0_z=6z^5. At fixed q,z or fixed H,z as appropriate,

    C_H=z nu/8,
    C_q=1/3+z[(3q^2-z/4)/s+(-3q^2-z/4)/d]/4,
    C_z=(s+d)/4-z(q/4+3z^5)nu/4.

Three exact contractions are

    mu C_H=zq^3/(2w^2),
    mu C_z=q^3/w-zq^3(q/4+3z^5)/w^2,
    mu(C-q/3)=zq^3/w.

The right sides lie on the third quotient

    w^2=(K0+zq/2)^2-4q^6.

Thus the terms produced by the physical C derivatives do not require
treating the two elliptic factors as independent invariant densities. The
mixed products are carried explicitly into this genus-two field.

## Exact elliptic H reduction

For a=+2 use s_a=s, and for a=-2 use s_a=d. Put

    f_a=a q^3-zq/2-K0,
    Delta_a=27a K0^2-z^3/2,
    A_a=9a K0/(2 Delta_a), B_a=3az/(2 Delta_a),
    R_a=(z^2+9aK0 q-3az q^2)/Delta_a.

The literal one-form identity is

    partial_H(dq/s_a)
      =(A_a+B_a q)dq/s_a+d_q(R_a/s_a).

It includes the actual K0_H=-1. Define

    T=R_-/d-R_+/s,
    G=(A_-+B_-q)/d-(A_++B_+q)/s.

Then mu_H=partial_q(T)+G on the physical background curve. Both G and
T are anti-invariant under (s,d)->(-s,-d); they have not been set to zero.

## Source-carrying H/q current and exact remaining correction

In the compact endpoint module take the three-form current

    J=-mu*omega0*dq^dz/72-T*omega0*dH^dz/72.

Its complete derivative gives

    S=dJ+[G*omega0+(mu C_H-T C_q)*nabla_C(omega0)]
             *dH^dq^dz/72.

For example, the H derivative of omega0 is
`nabla_H|C omega0+C_H*nabla_C omega0`, and the q derivative is
`C_q*nabla_C omega0`. These are the terms responsible for the correction;
they are included in the identity.

This identity is written in the relative compact de Rham module. The
literal endpoint fiber primitives from the stored Dwork reductions must be
transported with J to obtain a literal rational differential identity.
The exact elliptic reductions in the previous section are already literal.
No endpoint second-kind or fiber correction is declared zero.

Let L_+=3q^2-z/4, L_-=-3q^2-z/4 and f_+=s^2,f_-=d^2. The remaining
C coefficient splits exactly as

    mu C_H-T C_q=-T/3+Qinv,

    Qinv=zq^3/(2w^2)
       -z/4[(R_- L_+-R_+ L_-)/w
             +R_- L_-/f_--R_+ L_+/f_+].

Every coefficient in Qinv is a rational function of q,w,K0,z. This is the
explicit invariant correction on the background genus-two quotient. The
anti-character correction `G omega0-(T/3)nabla_C omega0` also remains.

The quotient belongs to the same universal genus-two family as the
endpoint, now with parameters (Hprime,Cprime)=(K0,z/2). Its physical
parameter transport is

    D_H=-nabla_Hprime,
    D_z=6z^5*nabla_Hprime+(1/2)nabla_Cprime.

The existing exact rank-four connection and its Dwork lifts can therefore
be reused on this quotient. They do not identify its Jacobian with the
separate endpoint Jacobian at (H,C). If Qinv is reduced in that compact
basis, differentiating the resulting primitives against the endpoint
column creates further C_q derivatives; those terms must remain in a
coupled current.

`elliptic_coupling_transfer.py` verifies 17 exact source, physical
derivative, elliptic-Hermite, character and two-current identities. Its
output is `elliptic-coupling-transfer-results.json`. The finite H/q
homotopy exposes a precise remaining correction, rather than cancelling
it or supplying a solution.
