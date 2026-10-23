# Exact background elliptic connection, including fiber corrections

For either elliptic source factor use

```
y^2=Aq^3+Bq+D, omega0=dq/y, omega1=q dq/y,
Eplus: A=2, Eminus: A=-2,
B=-z/2, D=H-1-z^6, DeltaE=4B^3+27A D^2.
```

The matrices have columns indexed by the differentiated basis element:

```
M_D = 1/DeltaE * [[-9AD/2, -B^2],
                  [-3AB,    9AD/2]],
M_B = 1/DeltaE * [[-B^2,    3BD/2],
                  [ 9AD/2,   B^2]].
M_H=M_D, M_z=-M_B/2-6z^5 M_D.
```

These are cohomological connections. The exact identities have the form
`partial_parameter omega_j = sum_i M_ij omega_i + d_q(R_j/y)`.
All four explicit degree-two polynomials R_j are saved in
`background-elliptic-connection.json`. Integrating these exact terms against
the endpoint kernel generates derivatives of that kernel and of its full
physical C. Those corrections must be retained.

The exact Euler identities are

```
4B M_B+6D M_D=diag(-1,1),
6(H-1+3z^6) M_H+4z M_z=diag(-1,1).
```

At fixed H,z the apparent q^2 terms in the companion translation reduce as

```
q^2 dq/s = ds/3+(z/12)dq/s,
q^2 dq/d = -dd/3-(z/12)dq/d.
```

The generator `derive_background_elliptic_connection.py` proves all four
polynomial fiber reductions, flatness, and both physical Euler identities:
eight exact symbolic groups pass. This is constructive connection data for
the actual elliptic source; it does not supply the endpoint primitive.
