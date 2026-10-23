# A source-derived exact change of the free Y-current

This supplies an actual alternative horizontal current and its complete
remaining forcing. It does not solve the fourth-order matching equation.

Use q=3C−3az/2, rho=q^3/a^2, and the ordinary density primitive

    R=−27C^3/a+(81/4)Cz^2a−(27/16)z^3a^2,
    W_R=−81C^2z^2/(4a).

Exactly,

    partial_a R+partial_z W_R=rho.

Let E_R=R partial_a+W_R partial_z and J_R=E_R(H)=H_a R+H_z W_R.
On the rational open J_R≠0 define

    U_R=−rho R/(6J_R),
    W_new=−rho W_R/(6J_R).

Then H_a U_R+H_z W_new=−rho/6, precisely the required actual source flux.
For the previously supplied source-guided currents U0,W0, the exact free
Hamiltonian correction is

    S_R=(R W0−W_R U0)/J_R,
    U_R=U0+S_R H_z,
    W_new=W0−S_R H_a.

Consequently

    D_R=partial_a U_R+partial_z W_new
       =D0+Y(S_R),
    D0=partial_a U0+partial_z W0,
    Y=H_z partial_a−H_a partial_z.

The complete remaining source has the source-driven rational expression

    D_R=[rho E_R(J_R)−J_R E_R(rho)−rho^2 J_R]/(6J_R^2).

The equivalent equation retains an independent correction S_new:

    Lhat_delta*G=D_R+Y(S_new),
    S_total=S_R+S_new.

The J_R normalization introduces ordinary C-poles and is not a standalone
one-direction ODE target. The independent correction S_new remains essential;
the original polynomial-C Euclidean currents already avoid those J_R poles.
No actual pair G,S_new is supplied. Every J_R contribution and compact row
must be retained.

`verify_density_Y_transport.py` checks the exact density identity and the
algebraic source-flux/current-change identities; it performs no search.
