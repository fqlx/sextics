# Source potential and physical symplectic volume

This records two exact constructive identities. It does not give a rational
current for the physical source.

Use the full diagonal quotient and orientation from
`../../../cubic-ray/INTERFACE.md`:

```
H=1+z^2+t,
B=U/2+K/3+z*U*K/2,
C=z^(-2)+U^6+K^6/t,
f=H+B*p+C*p^3,
g=3*C*p^2+B,
rho=1/(18*t*z^2).
```

The actual residue is `R*Omega`, where

```
R=B*p/g^3,
Omega=rho*dz dU dK dt.
```

All identities below retain this source and this density.

## An elementary coefficient potential

In the cubic field, with H and C held fixed, implicit differentiation gives

```
p_B=-p/g,
p_BB=2*B*p/g^3,
F_B=-p/(2*g),
partial_B(F_B)=R.
```

Thus a physical vector field V satisfying

```
V(H)=V(C)=0, V(B)=1, div_Omega(V)=0
```

would yield the source current `F_B*V`. This is a conditional statement:
no such rational V has been constructed. Requiring a lift of the pure
coefficient direction is stronger than the full rank-two current problem;
the fixed-H,C fibers have nontrivial geometry. This potential is therefore
not a certificate or a proof that this restricted lift exists.

## A rational symplectic form with the actual source volume

The closed rational two-form

```
omega=dz wedge dU/(3*z^2)+dK wedge dt/(6*t)
```

satisfies `omega^2/2=Omega`. With the convention

```
{F,G}=3*z^2*(F_z*G_U-F_U*G_z)
      +6*t*(F_K*G_t-F_t*G_K),
X_F(G)={F,G},
```

every rational base Hamiltonian F gives

```
X_F=(-3*z^2*F_U, 3*z^2*F_z, -6*t*F_t, 6*t*F_K),
div_Omega(X_F)=0.
```

The four coordinate Hamiltonians give a rational frame on `z*t != 0`:

```
X_z=3*z^2*partial_U,
X_U=-3*z^2*partial_z,
X_K=6*t*partial_t,
X_t=-6*t*partial_K.
```

In particular,

```
{H,C}=36*(z^3*U^5-K^5).
```

Consequently H and C are not simultaneous Casimirs of this bracket. The
bracket gives physical divergence-free fields using all four directions;
it does not automatically lift `partial_B` or the universal W2 field.

For any rational a in the cubic field, the current `a*X_F` has divergence
`X_F(a)`, where base derivations extend by `D(p)=-D(f)/g`. Hence the exact
source equation can constructively be sought as

```
sum_j X_(F_j)(a_j)=B*p/g^3.
```

This keeps both coefficient variation and the physical density. No
rational choices of the a_j and F_j satisfying this equation are supplied
here. The rank-two physical current equation in the interface remains
open.

## A bracket retaining all three coefficient variations

Extend the same Poisson bracket to the cubic field by its unique algebraic
extension, equivalently by the implicit derivatives
`D_i(p)=-(H_i+p*B_i+p^3*C_i)/g`. Then the actual coefficient potential
`p_B=-p/g` obeys

```
{p,p_B}=-p*(3*p^2*{H,C}+2*p^3*{B,C}+{H,B})/g^3.
```

Here the bracket includes the physical H, B, and C; none of those
coefficient directions has been frozen. This gives a concrete bracket
whose denominator and cubic character match the source. Cancelling its
additional coefficient brackets to obtain `B*p/g^3` remains open.

Run `verify_source_potentials_and_poisson.py` for the seven standalone
symbolic checks in `source-potentials-and-poisson-checks.json`.
