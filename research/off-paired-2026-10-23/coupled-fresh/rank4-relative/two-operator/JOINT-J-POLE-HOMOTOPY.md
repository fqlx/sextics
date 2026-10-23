# Exact joint pole homotopy for the E-current

This is a finite rational integration-by-parts construction, not a new
standalone ODE target. The already supplied S_E removes the source's J poles;
the regular D0 forcing remains the essential problem.

Let E=a partial_a−z partial_z, J=E(H), rho=q^3/a^2, and

    D_E=A_source/J^2,
    A_source=rho(8a^2+24z^6−qz/2)/6.

Work on the actual rational open Y(J)≠0, with

    Y=H_z partial_a−H_a partial_z,
    R_Y(F)=Y(F/Y(J)).

For every n≥1 the exact identity is

    F/J^(n+1)
      =−Y[F/(nY(J)J^n)]+R_Y(F)/(nJ^n).

It differentiates every coefficient, including Y(J); no held-constant
Jacobian assumption is used.

## A finite joint G,S construction

For any proposed rational numerator g, write G=g/J and expand the ordinary
normal-ordered adjoint as

    Lhat* =sum_(n=0)^4 a_n delta^n,  a4=1,
    Lhat*(g/J)=sum_(k=0)^4 F_k/J^(k+1).

The F_k are explicit rational expressions determined by the finite Leibniz
recurrence. If g_j=delta^j g and J_j=delta^j J, the leading term is

    F4=24g J_1^4.

Define

    R_g=sum_(k=0)^4 R_Y^k(F_k)/k!,
    S_g=−sum_(k=1)^4 sum_(j=0)^(k−1)
          [(k−j−1)!/k!] R_Y^j(F_k)/(Y(J)J^(k−j)).

Then exactly

    Lhat*(g/J)=Y(S_g)+R_g/J.

In particular the leading joint correction is

    S_g=−6g(delta J)^4/[Y(J)J^4]+lower J-pole order.

The source itself has the exact reduction

    S_D=−A_source/[Y(J)J],
    D_E=Y(S_D)+R_Y(A_source)/J.

Thus a genuine source-derived g for which R_g=R_Y(A_source) would yield the
actual pair G=g/J, S_new=S_g−S_D. If equality holds only modulo J, the
remaining regular term must still be retained and integrated. All Y(J) poles
introduced by the construction remain obligations.

## Why this does not settle the source

The exact existing identity D_E=D0+Y(S_E), with D0 having no J denominator,
shows that the entire source J-principal part is already Y-exact. Its local
simple-pole residue after the displayed homotopy therefore vanishes modulo
J; the reduction returns a regular forcing rather than eliminating D0.
Geometrically E becomes proportional to Y on J=0 because both annihilate H
there. A proposed g/J must address the actual remaining regular class, not
merely cancel poles that S_E already removes.

`verify_joint_J_homotopy.py` checks the exact rational identity for n=1,...,4,
including all coefficient derivatives, and the fourth-order leading term.
