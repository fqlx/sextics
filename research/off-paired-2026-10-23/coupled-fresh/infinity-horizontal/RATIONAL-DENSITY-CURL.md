# Rational density primitive with the full endpoint correction retained

This removes logarithms from the choice of ordinary density primitive. It
does not remove the endpoint source or its horizontal residue obligation.
It is compatible with every source-matching Ore gauge.

Use the actual physical coordinates and derivations from the rank-four
closure, and put

```
v=a z, q=3C-3v/2, rho=q^3/a^2, alpha=2C/(3H),
T=D_H+alpha D_C, theta=C D_C, phi=rho D_H(a)=q^3/P_a.
```

The rational one-form and its exact full derivative are

```
eta= -q^3/(2a^2) dv,
d eta = rho da wedge dz -9q^2/(2a^2) dC wedge dv.
```

At fixed C its derivative is precisely `phi dH wedge dz`. At fixed normalized
modulus, `dC=alpha dH`, the second term remains. It must not be discarded.
Define rational coefficients

```
Pe=rho T(v)/2, Qe=rho D_z(v)/2,
J=alpha[9q^2 D_z(v)/(2a^2)-rho D_C(a)].
```

Then exactly

```
phi=D_z Pe-T Qe+J.
```

For any of the homogeneous source-matching infinity operators B which commute
with T and D_z, the physical corrected source has the explicit partial curl

```
B(phi_H/6) = D_z P-T Q+B theta(K)/(9H^2),
P= -B theta(Pe)/(9H),
Q= -B theta(Qe)/(9H)-B phi/6,
K=Qe-HJ
 =q^2/a^2 (q/2-3C) D_z(v)+(2C/3)rho D_C(a).
```

The last term is fully retained. For the elementary-shifted original-source
convention, remove `-B phi/6` from Q. No rational curl or closed ambient
two-form carrying the remaining term has yet been supplied.

The same density primitive is the bare-coordinate vector

```
R_e=-q^3/(2a), W_e=z q^3/(2a^2),
partial_a R_e+partial_z W_e=rho.
```

Equivalently `E=a partial_a-z partial_z` has `E(q)=0`, `div(E)=0` and
`E(rho)=-2rho`. Its normalized source flux gives

```
J_E=E(H)=2a^2-2q^6/a^2-6z^6-qz/2,
U_E=-rho a/(6J_E), W_E=rho z/(6J_E),
div(U_E,W_E)=rho[8a^2+24z^6-qz/2]/(6J_E^2).
```

This is an explicit free-Hamiltonian shift of the earlier source Bezout
current. Its ordinary critical poles mean it is not an independently solved
fourth-order ODE. Genuine additional corrections remain necessary.

`verify_rational_density_curl.py` checks six exact symbolic groups, including
the physical density identity for arbitrary a(H,C,z), the complete source
curl with its remainder, and the bare Euler simplification.
