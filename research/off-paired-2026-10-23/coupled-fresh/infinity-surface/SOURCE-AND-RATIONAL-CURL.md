# Actual infinity-surface source and a rational density partial current

No complete closed infinity two-form or certificate is supplied. This note
records the exact source on the normalized surface and the log-free partial
current obtained from the parent agent's ordinary density primitive. Its
remaining rational density is explicit and has not been cancelled.

`verify_source_rational_curl.py` passes fifteen exact standard-library Fraction
groups. `evaluate_rational_curl.py` checks the resulting B12 partial current
on an actual implicit branch, with all six required C derivatives retained.

## Actual surface source

Use the existing physical finite field

    q=3C-3az/2,
    P=a^4+q^6+a^2(z^6+qz/2+1-H)=0,
    phi=q^3/P_a,
    T=D_H+2C D_C/(3H), theta=C D_C.

Here `a=x^3`, not the original X2 coordinate. On the finite root cover put
`tau^3=H`, `b=C/tau^2`. Then T is differentiation in H at fixed b,z;
theta is `b partial_b` on the actual implicit coefficient field. An operator
`B=Vop*` whose coefficients are functions of b commutes with T and D_z.
The original Ore B and the source-gauged B12 are of this form.

For `sigma_original=-C D_C(phi)/(9H)` and `xi=B(sigma_original)`, one has

    xi dH wedge dz
      =Res_P -B[(b/(3tau)) partial_b(q^3/P)]
                da wedge d tau wedge dz.

This includes all implicit a derivatives. For example, the simple/double
pole normal residue of `partial_b(Q/P)`, `Q=q^3`, is exactly

    Q_b/P_a-(1/P_a)partial_a(Q P_b/P_a),

which equals the full derivative of `Q/P_a` using
`a_b=-P_b/P_a`. This identity iterates for every ordered derivative in B.
The factor is `b/(3tau)` because
`sigma_original=-b partial_b(phi)/(9tau^3)` and `dH=3tau^2 d tau`.

There is an explicit ambient identity, with F=q^3/P,

    theta_b F=(tau/2)partial_tau F
                 -(3/2)a^2 tau^3 q^3/P^2,

and therefore

    -B(theta_b F)/(3tau) da d tau dz
      =d[B(F) da wedge dz/6]
           +B[a^2 tau^2 q^3/(2P^2)] da d tau dz.

The residue of the double-pole term is precisely the previously known
corrected source `B(phi_H|C/6)dH dz`. This identity is the established
elementary source-convention change in surface form; it is **not** a new
primitive or a new cancellation of that corrected source.

## Parent's rational ordinary density primitive

Set

    v=az, rho=q^3/a^2, k=9q^2/(2a^2),
    eta=-rho dv/2.

Its full ordinary differential in a,C,z is exactly

    d eta=rho da wedge dz-k dC wedge dv.

On a normalized leaf b fixed, `dC=alpha dH`, `alpha=2C/(3H)`. Define

    eta_H=-rho T(v)/2, eta_z=-rho D_z(v)/2,
    L=k D_z(v)-rho a_C.

Then

    phi dH dz=d_leaf(eta_H dH+eta_z dz)+alpha L dH dz.

All physical derivatives remain. In particular,

    a_C=-P_C/P_a, a_z=-P_z/P_a,
    T(a)=(a^2-alpha P_C)/P_a.

Exact polynomial reduction using P=0 gives the smaller expression

    L=q^2(9H-36z^6-9-21qz/4)/P_a.

## Explicit rational curl and its remaining density

Put `Aop=B theta` and

    J=eta_z+(2C/3)L,
    Peta=Aop(eta_H)/(9H),
    Qeta=Aop(eta_z)/(9H),
    Seta=-Aop(J)/(9H^2).

The exact source-carrying identity is

    xi_original=D_z(Peta)-T(Qeta)+Seta.

The derivative of `1/H` is essential. Keeping it produces the `eta_z` term
in J; omitting it would falsely simplify the remaining density. The proof
only uses the leaf identity above and `[Aop,T]=[Aop,D_z]=0`, so it applies
also to B12, with its associated compact Ore gauge retained separately.

The entire rational J is explicitly

    J=q^2/(12P_a)*[
         36H(az+q)-24a^2q-21aqz^2-144az^7-36az
         -17q^2z-72qz^6-36q ].

No undifferentiated logarithm occurs. These current coefficients are rational
over the original coefficient field; the tau cover was useful to state the
surface interpretation but is not needed to define this partial current.

For the corrected source `B(phi_H|C/6)`, replace Qeta by
`Qeta-B(phi)/6`; Seta is unchanged.

Equivalently, this gives an actual globally closed rational two-form

    beta_partial=d[Aop(eta_H dH+eta_z dz)/(9H)],

whose restriction to the leaf is

    beta_partial|leaf=(-xi_original+Seta)dH dz.

Full d includes the normal coefficient derivative. The remaining task is
a closed rational `beta_remaining` with restriction `-Seta dH dz`; it need
not be exact. Closed logarithmic two-forms and other nontrivial closed
classes are still allowed.

## Check of this candidate and precise stopping point

The source-gauged operator used for the concrete check is

    B12=1/630 * {
      (C^3/H^2)(44theta^2-35)
       -(729H^2/C^3)(11theta^2-39)
    } (2theta+3)(theta-1)(theta-2).

At the actual point `(a,C,z,H)=(1,1,1,969/64)`, the independent implicit
Taylor calculation has P identically zero through order six. The retained
Seta is

    -26844196695165812755131673402579281672733355141356732959641
    /37004743205030066760424019651068076737970847587095019520.

Thus this particular partial current does not yet close. This is a direct
candidate check, not an ansatz or all-pole nonexistence result.

No further rational Griffiths reduction or closed logarithmic extension was
obtained here. In particular, no conclusion about nonmembership of the
surface source, its Hodge type, or the existence of some other closed
extension is asserted. Such an extension remains the constructive target.

## Verified elliptic source decomposition at fixed H,z

The infinity agent subsequently supplied a new positive source decomposition.
Set `K=1+z^6-H` and regard q as the curve variable. Then

    P=a^4+a^2(K+zq/2)+q^6,
    b0=q^3/a, s=a+b0, d=a-b0,
    s^2=2q^3-zq/2-K,
    d^2=-2q^3-zq/2-K.

The independent polynomial checks verify both elliptic equations. With
`P_aq` denoting the a derivative at fixed q (different from physical P_a at
fixed C), one has on P=0

    P_aq=2a s d,
    P_a|C=P_aq-(3z/2)P_q,
    dC=(P_a|C)/(3P_aq)dq.

Consequently the **actual** source differential is exactly

    phi dC=(dq/12)(1/d-1/s).

The one-twelfth and sign were independently checked by clearing the complete
quartic relation. No density or endpoint coefficient has been replaced by a
trace surrogate.

For generic H,z the two cubics have distinct disjoint finite branch sets and
share the infinity branch. The common biquadratic curve therefore has genus
four. Its third quadratic quotient is

    w=s d,
    w^2=(K+zq/2)^2-4q^6,

which is the endpoint genus-two family at parameters `(K,z/2)`. The displayed
source is odd under simultaneous `(s,d)->(-s,-d)` and uses the two elliptic
components of the common curve. This is a source-specific decomposition.

The physical coefficient is still `C=q/3+z(s+d)/4`. It couples both elliptic
points to the endpoint connection. The decomposition therefore supplies a
useful actual source interface, without integrating the complete endpoint
kernel or supplying the missing closed extension.

No certificate has been found.
