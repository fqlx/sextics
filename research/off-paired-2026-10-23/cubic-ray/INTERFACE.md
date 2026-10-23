# The actual source on a cubic cover

This is an exact reformulation, not a primitive or certificate.

On the chart `X0=1`, write

```
X1=x, X2=a, Y0=y, Y1=y*u, Y2=y*v, s=y^2,
H=1+x^6+a^6,
B=x*u/2+x^3*a*u*v/2+x*a*v/3,
C=1+u^6+v^6,
f(s)=H+B*s+C*s^3.
```

The order of the original affine volume is
`dx da dy dY1 dY2`. The coordinate substitution gives

```
A*volume/F^2 = s^2/(2*f^2) * dx da ds du dv.
```

Indeed, the three Y-coordinate Jacobian is `y^2`, and
`y^5 dy=s^2 ds/2`. This retains the exact target `A=y^3`.
The involution negating all Y coordinates fixes this differential; its
invariant function field is precisely the cubic field below.

## Normal residue and finite connection

Fix a characteristic-zero constant field k. For the unrestricted complex
certificate problem use `k=ℂ`; the rational search data use `k=ℚ`.
Let `K=k(x,a,u,v)`, let `L=K[s]/(C*s^3+B*s+H)`, and put
`g=3*C*s^2+B`. With `df` placed first, the residue four-form is

```
R * mu,  mu=dx da du dv,
R=(1/g)*partial_s(s^2/(2*g))=B*s/g^3.
```

There is no orientation change: moving `ds` past the two X-coordinate
differentials has positive sign. Equivalently

```
R= -B/(6*C) * partial_H^2(s),
```

where H, B and C are treated as independent coefficients before physical
pullback. Its field trace is zero: the three residues sum to minus the
residue at infinity of `s^2 ds/(2*f^2)`, which is zero.

Use the trace-free basis

```
e1=s, e2=s^2+2*B/(3*C).
```

Every rational function in L has a unique expression in `1,e1,e2`.
Derivations of K extend uniquely to L and commute with field trace.
Consequently an arbitrary rational primitive can be averaged under the
Y-sign involution, descended to L, and then projected to trace zero without
changing its derivative R*mu. Thus the rank-two current equation is an
unrestricted reformulation of rational exactness on this chart; it does
not restrict endpoint pole positions or denominator degree.

The independently generated matrices are in
`../endpoint/cubic-ray/`; columns are derivatives of basis elements. If
`D_i(e_j)=sum_k M_i[k,j]*e_k`, the current equation is

```
sum_i (partial_i b_i + M_i b_i) = r,
```

where `R=r1*e1+r2*e2` and `M_i=H_i*M_H+B_i*M_B+C_i*M_C`.
All four base directions `(x,a,u,v)` are available. Restricting to a subset
of them would be a new sufficient ansatz, not the full equation.

## Conditional lift to the physical certificate

Suppose actual rational elements `a_i in L` satisfy
`sum_i D_i(a_i)=R`. Choose rational representatives in the ambient
variables `(s,x,a,u,v)`, with denominators nonzero modulo f, and put

```
A0=s^2/2,
V_qi=-g*a_i,
V_s=A0/g+sum_i f_qi*a_i.
```

Then `V(f)=A0` identically in the ambient field, and modulo f

```
div(V)=g*(R-sum_i D_i(a_i))=0.
```

Here `D_i=partial_qi-(f_qi/g)*partial_s`. The formula retains the
derivative of the normal Jacobian g; omitting it would change R.

The physical substitution has Jacobian
`J=det d(x,a,s,u,v)/d(x,a,y,Y1,Y2)=2/y`.
The Piola pullback `W=J*(d theta)^(-1)*V` is

```
W_X1 = 2*V_x/y,
W_X2 = 2*V_a/y,
W_Y0 = V_s/y^2,
W_Y1 = 2*V_u+Y1*V_s/y^3,
W_Y2 = 2*V_v+Y2*V_s/y^3.
```

It satisfies `W(F)=y^3` and `div(W)=0 mod F`. Clearing a common
denominator D not divisible by F therefore gives

```
A*D^2-D*sum(N_i*F_i)+F*(D*div(N)-N(D)) = F^2*Q.
```

The remaining homogenization and complex coprimality requirements are
the ordinary original-target ones; insert the X0 component as zero.
Every proposed solution must still be cleared, checked exactly as a
polynomial identity, and formally verified. No current solving the
rank-two equation has been found.

## An explicit universal primitive and its physical obligation

The endpoint agent derived the coefficient-space vector field

```
W2= -2*B^2/(3*C)*partial_H + 3*H*partial_B,
Delta=4*B^3+27*C*H^2,
F0=(3*C*s^2-B)/(10*g^3).
```

In the cubic field, `W2(Delta)=0`, `W2(g)=s*g`,
`Delta=g^2*(g+3*B)`, and **`W2(F0)=R`**. This is a rational
primitive along the universal coefficient flow, retaining the actual
source R. It does not yet preserve the physical four-dimensional volume.

There is a concrete sufficient scalar correction problem. Write

```
J=H_x*B_a-H_a*B_x,
Y_B=(B_a,-B_x,0,0), Y_H=(-H_a,H_x,0,0),
N2= -2*B^2/(3*C)*Y_B + 3*H*Y_H,
V0=N2/J.
```

Then `div(N2)=0`, `V0` lifts W2, and
`div(V0)=-N2(J)/J^2`. The divergence-free vertical Nambu field is

```
G=B_u*C_v-B_v*C_u,
K=(H_a*G,-H_x*G,J*C_v,-J*C_u).
```

It annihilates H, B and C. A rational solution of

```
K(h)=N2(J)/J^2
```

would give the divergence-free physical lift `V=V0+h*K`. The current
`a_i=F0*V_i` would then satisfy `sum_i D_i(a_i)=R`, and the previous
conditional lift would produce the certificate. Rational solvability of
this scalar equation is open. A rational primitive of the full rank-two
system need not arise from this particular flow.

## Full diagonal quotient with a low-degree cubic

The order-six symmetry on `(a,v)` has invariant coordinates `k=a*v,t=a^6`.
It gives `mu=dx du dk dt/(6*t)`. The remaining order-three diagonal action
on `(x,u,k)` is removed by

```
z=x^3, U=u/x, K=k/x, p=s*x^2.
```

The resulting cubic is

```
f=H+B*p+C*p^3,
H=1+z^2+t,
B=U/2+K/3+z*U*K/2,
C=z^(-2)+U^6+K^6/t.
```

The full physical five-form is exactly

```
p^2/(36*t*z^2*f^2) * dz dU dK dt dp.
```

Here `(z,U,K,t,p)` as rational functions of the original affine variables
are `(x^3,Y1/(x*y),a*Y2/(x*y),a^6,x^2*y^2)`. Their Jacobian determinant
in original order `(x,a,y,Y1,Y2)` is `36*t*x^2/y`. Multiplying the new
source coefficient by this determinant gives the original `y^3`.

The residue is `rho*R*dz dU dK dt`, with
`rho=1/(18*t*z^2)` and the same universal `R=B*p/(3*C*p^2+B)^3`.
Thus the exact trace-free current equation becomes

```
sum_i [partial_i b_i + M_i*b_i + ell_i*b_i] = r,
(ell_z,ell_U,ell_K,ell_t)=(-2/z,0,0,-1/t).
```

This retains the density as a logarithmic derivative rather than discarding
it. All 36 diagonal symmetries preserve the target differential, so
averaging makes this quotient formulation complete as well. Its simpler
coefficients may be useful for constructing currents. It is not a new
claim of exactness.
