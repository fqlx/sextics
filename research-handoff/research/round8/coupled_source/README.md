# Actual cyclic source in the full transverse rank-three connection

This is a constructive source/current reduction outside the obstructed
one-direction scalar route. No primitive or certificate has been found.

## Exact source-compatible quotient

Put `X0=h,X1=v*h,X2=W,Y0=a*y,Y1=b*y,Y2=y,t=y^2`, and `c=5/7`.
The original sextic is exactly

```
C=W^6+c(h^3+B*h*t)W^3+P*h^6+Q*h^4*t+R*h^2*t^2+S*t^3,
B=b(1+av), P=1+v^6, Q=cabv, R=c(ab+vb^3), S=1+a^6+b^6.
```

On the chart h=1 the affine Jacobian is y^2, so the **actual** target
`X0^3Y0^3 Omega/F^2` descends exactly to

```
(a^3/2)*h^4*t^2*Omega_(h,W,t)/C^2 wedge da db dv.
```

Here `Omega_(h,W,t)|h=1=dW wedge dt`; this fixes the orientation convention.
`direct_source.py` checks both the literal six-variable substitution and
the Jacobian identity.
The independent parent replay
`/workspace/research/round9/cyclic_full/independent_physical_source.py/json`
also reads the pinned `instance.rec` and verifies the full affine Jacobian
`h*y^2`, positive source sign, and canonical prefactor exactly over QQ.

Set

```
beta=-R/(3S), A=3S-BR, M=A/(3S), alpha=M/B,
t_old=alpha*T+beta*h^2, W_old=rho*W, rho^3=M.
```

Then `C_old=M^2*C_new`, with

```
L=(27PS^2-9QRS+2R^3)/(3A^2),
r=(3SQ-R^2)/(BA), x=3B^3/A,
C_new=W^6+c(h^3+hT)W^3+Lh^6+r h^4T+T^3/x.
```

The source becomes `rho*g0*(alpha*T+beta*h^2)^2*h^4 Omega/C_new^2`,
where `g0=a^3/(2BM^3)`. The cubic-root character is retained.

## Full source and the missing multiplier derivatives

Use `omega0=h^2 Omega/C`, `omega1=T Omega/C`. Parameter differentiation gives

```
eta(1)=-nabla_L omega0,
eta(T)=-nabla_r omega0,
eta(T^2)=-nabla_r omega1.
```

Thus the source is exactly

```
-rho*g0[alpha^2*nabla_r omega1
        +2alpha*beta*nabla_r omega0+beta^2*nabla_L omega0].
```

The verified three-direction actual connection and all fiber-exact
corrections are in `/workspace/research/round9/cyclic_full/actual_fast.pickle`.
Its convention is `nabla_j beta=N_j beta` for the basis column. Coefficient
columns therefore differentiate by `d_j+N_j^T`.

Let `V_L,V_r,V_x` be the pulled-back coordinate fields and
`Jac=det d(L,r,x)/d(a,b,v)`. Native exact factorization yields

```
Jac=(1215/343)*b^2*(1+av)*S^2*Delta47/A^5.
```

`jacobian_native.pickle` supplies polynomial dictionaries in `(a,b,v)`,
including `Delta47`; `coordinate_fields.pickle` supplies all three fields as
reduced rational pairs. The native determinant and factorization identities
are checked exactly by `factor_jacobian.py`.

Define

```
fT=3a^3S/(2B^3A), z=BR/A, H=rho*fT/Jac.
```

Then the complete coupled divergence equation for coefficient vectors Z_j
of the 3-current `rho*fT*Z_j` along V_j is

```
sum_j [V_j(Z_j)+N_j^T*Z_j+(V_j log H)*Z_j]
  =-N_r^T e1+2z*N_r^T e0-z^2*N_L^T e0.
```

The logarithmic term is explicitly

```
dlogH=3da/a+(13/3)dA/A-5db/b-4d(1+av)/(1+av)
      -(4/3)dS/S-dDelta47/Delta47.
```

It includes both rho and all base multiplier derivatives. Dropping this term
would reintroduce the source error that the coupled construction is meant to
avoid. The fixed first integration by parts is
`Z_r=-e1+2z*e0`, `Z_L=-z^2*e0`, `Z_x=0`. Its two holomorphic residuals are
nonzero at three exact rational base points; the fractions are recorded in
`source_model.json`. They must still be removed by a new coupled current.

Reproduce with `python direct_source.py` and `python factor_jacobian.py`.
All files are scratch research outside the protected repository.
