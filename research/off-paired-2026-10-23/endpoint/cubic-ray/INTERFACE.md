# Actual cubic-ray source and complete finite connection

In the chart `X0=1`, put

```
X1=x, X2=a, Y0=y, Y1=y*u, Y2=y*v, s=y^2,
H=1+x^6+a^6,
B=x*u/2+x^3*a*u*v/2+x*a*v/3,
C=1+u^6+v^6,
f=C*s^3+B*s+H,
T=f_s=B+3*C*s^2,
D=4*B^3+27*C*H^2.
```

The actual five-form becomes `s^2/(2*f^2) dx da ds du dv`: the coordinate
Jacobian is `y^2`, so the original numerator `y^3` gives
`y^5 dy=s^2 ds/2`. Moving `ds` to the front takes two swaps and keeps its sign.
Its double-pole residue, with `df/f` first, is

```
R = (1/T) d_s(s^2/(2*T)) = B*s/T^3 = -B/(6*C) d_H^2(s).
```

Fix a constant field `k` of characteristic zero and put `K=k(x,a,u,v)`.
Use `k=C` for the full certificate contract, which allows complex
coefficients. The matrices and source below are defined over `Q` and base
change verbatim to `k`; the modular searches only explore their rational
coefficient subfield and do not establish descent of complex solutions to
`Q`. This residue has trace zero for the separable cubic field
`L=K[s]/(f)`. The trace-free basis

```
e1=s, e2=s^2+2*B/(3*C)
```

has the following connection. Columns are derivatives of basis vectors;
`d_q e_j=sum_i M_q[i,j]e_i`.

```
M_H = [[9*C*H, 4*B^2], [-6*B*C, 18*C*H]]/D,
M_B = [[2*B^2, -6*B*H], [9*C*H, 4*B^2]]/D,
M_C = [[-(2*B^3+9*C*H^2)/C, 2*B^2*H/C],
       [-3*B*H, -2*(2*B^3+9*C*H^2)/C]]/D.
```

The source vector is

```
r = [B*(27*C*H^2-2*B^3), -27*B^2*C*H]/D^2.
```

`finite_connection.py` passed 43 exact symbolic identities, including the
field reductions, flatness, trace pairing, both Euler identities, and two
independent source expressions. This checks the algebraic connection and
residue formula; independent transport checks are retained in the audit
directory.

For `q=(x,a,u,v)`, define `A_i=H_i M_H+B_i M_B+C_i M_C`. A rational
trace-zero three-form primitive is exactly a collection of two-component
rational vectors `a_i` satisfying

```
sum_i (d_i a_i+A_i a_i)=r.
```

Here the three-form is `sum_i (-1)^i (e dot a_i) dq_0...omit(dq_i)...dq_3`.
This interface covers every rational primitive of the residue after averaging
the global Y-sign involution and projecting away the field trace. Indeed a
finite separable field extension has no relative differentials, so every
rational three-form lies in `L tensor Omega^3(K)`; trace commutes with `d`.
The averaging and trace statements hold over the fixed field `k`; they do not
descend its constants to `Q`. This completeness statement does not assert
that a primitive exists.

## An exact universal primitive and its physical correction

The universal parameter vector field

```
W2 = -2*B^2/(3*C) d_H +3*H d_B
```

preserves `C,D` and satisfies

```
W2(e1)=e2, W2(e2)=-2*B*e1/(3*C), W2(T)=s*T.
```

Using `D=T^2(T+3B)`, the rational trace-zero function

```
F0 = 1/(6*T^2)-D/(15*T^5)
   = (3*C*s^2-B)/(10*T^3)
   = 27*B^2*C*H/(5*D^2) e1
     -3*C*(8*B^3-27*C*H^2)/(10*D^2) e2
```

satisfies **`W2(F0)=R`**. This integrates the exact source along the universal
Möbius field; a physical divergence-free lift is still needed.

For the actual four-variable base put

```
J=H_x B_a-H_a B_x,
Q=B_u C_v-B_v C_u,
N2=-2*B^2/(3*C) (B_a d_x-B_x d_a)
   +3*H (-H_a d_x+H_x d_a),
K=(H_a Q,-H_x Q,C_v J,-C_u J).
```

Both `N2` and `K` have zero ordinary divergence. Moreover `N2(H,B,C)` is
`J*(-2B^2/(3C),3H,0)`, and `K(H)=K(B)=K(C)=0`. Every rational physical lift
of `W2` therefore has the form

```
V=N2/J+h*K.
```

It has zero divergence if and only if the following single rational equation
holds:

```
K(h)=N2(J)/J^2.                                      (* open *)
```

If such a rational `h` is found, the current `F0*(N2/J+h*K)` has divergence
exactly `R`. Without it, the explicit current `F0*N2/J` has divergence

```
R-F0*N2(J)/J^2.
```

`mobius_lift.py` passed 16 exact checks of these identities. No rational `h`
has been found. The lift equation is sufficient for the desired primitive;
failure to solve it would not rule out other currents in the complete rank-two
interface.

## The remaining one-dimensional equation

On a generic fiber of `(H,B,C)`, the rational one-form

```
omega=du/(C_v*J),  omega(K)=1,
```

turns the lift equation into

```
d_fiber h=(N2(J)/J^2)*omega.
```

The fiber sits in the product of the two Fermat curves
`x^6+a^6=H-1` and `u^6+v^6=C-1`, each of genus ten. If the projective
coordinates are `[t:x:a]` and `[w:u:v]`, its equation is

```
t^3*x*u*w/2+x^3*a*u*v/2+t^2*x*a*v*w/3-B*t^4*w^2=0.
```

It is a divisor of class `(4,2)` on this product, of arithmetic genus 613.
The displayed model has boundary singularities, including generically 36
ordinary nodes at `x=w=0`; arithmetic genus is not the genus of its
normalization. Thus no rational-fiber or elementary-integration conclusion
follows from the eliminations.

The exact finite quotient `k=a*v, t=a^6` gives another useful presentation:

```
H=1+x^6+t, C=1+u^6+k^6/t,
B=x*u/2+x^3*u*k/2+x*k/3,
volume=dx du dk dt/(6*t).
```

Its fixed `(H,B,C)` fiber eliminates `t,k` as

```
t=H-1-x^6,
k=(B-x*u/2)/(x*(3*x^2*u+2)/6),
(C-1-u^6)*(H-1-x^6)*(x*(3*x^2*u+2)/6)^6
  -(B-x*u/2)^6=0.
```

The quotient and its density must both be retained when transporting a
candidate. These formulas provide a lower-degree rational presentation;
they do not themselves supply the missing primitive.

## One focused finite-connection integration attempt

`simple_discriminant_current.py` tested `a_i=P_i/D` in the complete
two-component interface. The numerator degree bounds in `(x,a)` and `(u,v)`
were, respectively, `(5,2)` and `(3,4)` for `e1,e2` in the two X directions;
they were `(4,3)` and `(2,5)` in the two Y-ratio directions. This was one
1104-unknown ansatz, with no degree escalation or extra C-pole family.

The sampled modular system was inconsistent at 600 generic points over
`F_1009` (1200 rows, column rank 1104). No candidate was produced. This
limited search result does not decide exactness in the complete rational
interface, and does not close or disprove the scalar lift obligation above.
