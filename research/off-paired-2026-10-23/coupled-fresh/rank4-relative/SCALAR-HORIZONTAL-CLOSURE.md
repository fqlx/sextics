# Complete scalar closure of the full compact endpoint current

This is an exact constructive reformulation. A rational solution of the scalar
forced equation below has not yet been found. All four compact components and
all three physical base directions are retained. The equivalence concerns this
full four-component compact current system; it does not classify additional
moving-pole or third-kind extensions of the original rational primitive problem.

Use the conventions of `endpoint/CURRENT-INTERFACE.md`: the compact basis is
`omega_j=p^j dp/Z`, j=0,1,3,4, and source is

    r_original=−phi ∇H(omega0)/6,
    phi=q^3/P_a,
    q=3C−3az/2,
    P=a^4+q^6+a^2(z^6+qz/2+1−H)=0.

Here a=x^3 is the normal base variable, not the physical variable X2.
Every derivative below is the actual derivation on this physical finite field.

## Physical coefficient derivations

Write P_a=partial_a P with H,C,z held fixed. Then

    a_H=a^2/P_a,
    a_C=−[18q^5+(3/2)a^2z]/P_a,
    a_z=−[−9aq^5+a^2(6z^5−3az/4+q/2)]/P_a.

Thus, on arbitrary rational functions of (a,H,C,z),

    D_H=partial_H+(a^2/P_a)partial_a,
    D_C=partial_C−(P_C/P_a)partial_a,
    D_z=partial_z−(P_z/P_a)partial_a.

These derivations commute and preserve P. They include every physical
coefficient derivative; in particular D_C(a) and D_z(a) are not zero.

The exact corrected forcing is

    sigma_correction=phi_H/6,
    phi_H=[(2aq^3+3a^2q^2 q_a)P_a−a^2q^3P_aa]/P_a^3,
    q_a=−3z/2.

Alternatively, directly from the original source,

    sigma_original=−C D_C(phi)/(9H).

The two conventions differ by an explicit H-current as described below.

## Full cyclic basis and scalar Picard–Fuchs operator

Put s_j=∇C^j omega0, j=0,1,2,3, and Delta=4C^6−729H^4. Then

    s4=c0 s0+c1 s1+c2 s2+c3 s3,
    c0=−55C^2/Delta,
    c1=−309C^3/Delta,
    c2=−(271C^6−1458H^4)/(C^2 Delta),
    c3=−2(32C^6+729H^4)/(C Delta).

The cyclic matrix in the original compact basis has determinant

    −16533720 C^2 H^4/Delta^3,

so this is a basis over the complete rational coefficient field. The exact
H-connection is

    ∇H s_j=−[(2+2j)s_j+2C s_(j+1)]/(3H),

including j=3, for which s4 is reduced by the displayed relation. The
z-connection is zero in this universal cyclic basis; physical z derivatives
of coefficients remain D_z.

Define

    L=D_C^4−c3 D_C^3−c2 D_C^2−c1 D_C−c0,
    L* f=D_C^4 f+D_C^3(c3 f)−D_C^2(c2 f)+D_C(c1 f)−c0 f,
    T=D_H+(2C/(3H))D_C.

The full compact current equation is equivalent to the single scalar forced
adjoint equation with two arbitrary horizontal functions U,W:

    −L* f+T U+D_z W=sigma.

This equivalence places no restrictions on poles, degrees, or which physical
directions occur. It is a complete elimination, rather than a pure-component
ansatz.

## Explicit reconstruction

For any rational f,U,W solving this equation, define compact cyclic vectors

    u=(U,0,0,0),  w=(W,0,0,0),
    t3=f,
    t2=−D_C f−c3 f,
    t1=D_C^2 f+D_C(c3 f)−c2 f,
    t0=−D_C^3 f−D_C^2(c3 f)+D_C(c2 f)−c1 f,
    e=−2C/(3H),
    v=t−e u.

Then

    ∇H u+∇C v+D_z w=sigma s0.

For sigma=sigma_correction, add the explicit H-current −phi s0/6 to u.
The resulting full current has exactly the original source
−phi ∇H(s0)/6.

For sigma=sigma_original, instead add the explicit C-current
`C phi s0/(9H)` to v. This also gives precisely the original source.

No compact basis row is discarded in this reconstruction.

## Why the scalar equation is unrestricted

For a cyclic column b define

    E(b)=b0−D_C b1+D_C^2 b2−D_C^3 b3.

A vector b differs from E(b)s0 by an explicit C-current derivative, using

    B(b)=(b1−D_C b2+D_C^2 b3, b2−D_C b3, b3, 0),
    b−E(b)s0=∇C B(b).

Flatness permits arbitrary H- and z-current columns to be replaced by their
scalar reductions E(b)s0, with the discarded terms absorbed into the
C-current. For an arbitrary C-current, its scalar reduction is −L* applied
to its last cyclic component. Moreover E(∇H(U s0))=T U and
E(D_z(W s0))=D_z W. This proves both directions of the equivalence.

Equivalently, setting t=v+e u in the original full current gives component
rows

    ∇C t+(T−2j/(3H))u_j+D_z w_j.

The identity D_C^j(T−2j/(3H))=T D_C^j gives the same scalar elimination.

## Exact fiber corrections remain explicit

The identities above are cohomological in the compact endpoint module.
They lift to literal differentials using the exact Dwork primitives already
stored in `endpoint/reconstructed-connection.json`. If

    s_j=sum_k T_(k,j) omega_k+d_p(A_j/Z),

start with T_0=e0,A_0=0 and use the finite recurrence

    T_(j+1)=D_C T_j+M_C T_j,
    A_(j+1)=sum_k T_(k,j) R_(C,k)+partial_C A_j−A_j f_C/(2f),
    f=(H+Cp)^2−4p^6.

Thus L(omega0)=d_p((A_4−sum_j c_j A_j)/Z). The second-kind corrections
are retained, not declared zero. A scalar solution still requires this
ordinary Dwork transport and the original-target finite-certificate checks.

`verify_cyclic_closure.py` verifies the full rank-four companion relation,
all four H-columns, the weighted Euler connection, and the explicit adjoint
current. `verify_full_horizontal.py` additionally checks the physical
coefficient derivations and unrestricted horizontal reconstruction.

## Denominator-free Euler form

The parent agent additionally derived, and `verify_full_horizontal.py`
checks exactly, the useful identity

    L*(C^2 Delta g)
      =C^4(theta+4)^2(2theta−1)(2theta+5)g
       −729H^4 C^(-2)theta(theta−1)(theta+2)(theta+3)g,
    theta=C D_C.

This removes the coefficient discriminant denominators from the scalar
adjoint equation. Products denote composition; all factors in each displayed
product commute. The physical derivation D_C still acts on a as above.

For the H-connection, the literal exact correction in cyclic column j is
also finite and explicit. With N_H the cyclic H-matrix above, set

    B_(H,j)=sum_k T_(k,j)R_(H,k)+partial_H A_j−A_j f_H/(2f)
            −sum_ell (N_H)_(ell,j)A_ell.

Then

    partial_H s_j=sum_ell (N_H)_(ell,j)s_ell+d_p(B_(H,j)/Z).

For C, the first three cyclic columns have zero exact correction by their
literal derivative definition; the fourth has the displayed Picard–Fuchs
primitive A_4−sum c_j A_j. These formulas retain the exact second-kind
corrections through the complete scalar-to-four-component reconstruction.
