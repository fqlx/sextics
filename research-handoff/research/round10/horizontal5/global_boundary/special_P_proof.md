At the actual weighted corner, `v^6+1=0` adds no adjoint condition to the
generic corner ideal. This statement concerns the intermediate complete
intersection after the two previously verified blowups. It is not a claim
about every boundary of D32.

The calculation is over characteristic zero. Write `a0^6=v0^6=-1`,
`q=a0*v0`, `q^6=1`, and use the convergent formal coordinates

```
a=a0*(1-b_old*r_old)^(1/6),
v=v0*(1-nu)^(1/6),       nu=v^6+1.
```

After dividing D32 by `eps^17*b_old^2`, take the additional weighted blowup
with weights `(eps,W,b_old,r_old,nu)=(1,1,4,2,4)`. The strict equations have
orders 6 and 8. The literal 558-term graph gives the degree8 initial form in
`special_P_series.json`. The unit changes

```
B=a0*b_old, R=r_old/a0, n=a0^2*nu/q^2
```

and a nonzero constant rescaling of the second equation give the rational
initial complete intersection

```
F6=W^6+(5/7)*W^3*eps^3+B*(R+(5/7)*eps^2),
G8=B^2-(189/20)*B*R^2-(27/8)*eps^2*B*R
          +n*((3969/100)*R^2+(189/10)*eps^2*R).
```

These initial equations form a regular sequence, so the weighted strict
transform has precisely this complete intersection as its exceptional
divisor. The exact lower-term vanishing comes from the original graph,
not from a selected numerical fiber. The series truncation suffices here:
every new-weight-at-most8 monomial has old weight at most24, conductor
binomial order at most3, and `nu` exponent at most2. Those ranges are all
included by `special_P_series.py`.

The exceptional surface is smooth away nine Du Val points and the single
inherited corner at `[0:0:0:0:1]`. Here and below smoothness can be checked
on the finite orbifold covers of the weighted charts. If `eps=0,W!=0`,
`B*R=-W^6` implies `R!=0`, and `F_B` together with `G_n` gives independent
gradients. If `eps=W=0,R!=0`, then `B=n=0` and the same gradients work.
`B!=0,R=0` is impossible on G. The remaining point has only n nonzero.

On the `eps=1` chart the exact QQ Jacobian Groebner basis is saved in
`special_P_audit.log`. It forces precisely:

| R | B | n | W | type |
|---|---|---|---|---|
| 0 | 0 | 0 | 0 | A5 |
| 0 | 0 | 0 | W^3=-5/7 | three A1 |
| -5/7 | 0 | 0 | 0 | A2 |
| -10/21 | 0 | 0 | 0 | A2 |
| -10/21 | 15/28 | 75/784 | W^3=-5/14 | three A1 |

For an exact verification of the types, set `c=5/7` and
`K=W^3*(W^3+c)`. Except at `R=-c`, eliminate
`B=-K/(R+c)`. Up to the unit `(R+c)^2`, the remaining equation is

```
H=K^2+p(R)*K+n*g(R),
p(R)=(R+c)*R*((189/20)*R+27/8),
g(R)=(R+c)^2*R*((3969/100)*R+189/10).
```

At `R=0,-10/21`, g has a simple zero. The holomorphic splitting lemma in
the `(R,n)` pair reduces the singularity to the one-variable germ
`K^2+p(R_i)*K`. Its orders are respectively 6 and 2 at the two R=0 cases,
and 3 and 2 at the two R=-10/21 cases. At R=-c, G eliminates n and F is
exactly `K+B*(R+c)`, giving A2. Every nonvanishing coefficient and order is
checked symbolically in `special_P_audit.py`.

At the remaining n-chart point, use its finite mu4 cover and perform the
generic corner weighted blowup with weights `(3,2,6,6)` in
`(eps,W,B,R)`. Its initial complete intersection is

```
W^6+B*(R+(5/7)*eps^2),
B^2+(3969/100)*R^2+(189/10)*eps^2*R.
```

Its affine Jacobian singular ideal has dimension zero and colength83
over QQ. Thus it is quasismooth away its origin. The higher terms do not
introduce any lower old-weight term: the original family already has
orders `(12,12)` for the old weights at every v, as verified independently
by `../fresh/boundary/weighted_ci_audit.py`. The old-weight initial
coefficients in this chart are analytic in the new radial parameter,
and the displayed central quasismoothness persists near zero.

For completeness, the geometric inputs used after these exact calculations
are the usual extension facts for a weighted blowup of a complete
intersection: its canonical discrepancy is `sum(weights)-sum(degrees)-1`;
a quasismooth weighted strict transform has only finite quotient charts;
finite quotients of rational singularities in characteristic zero are
rational; and a deformation with Du Val special fiber has rational total
space. The latter follows from deformation invariance of rational
singularities over a smooth one-dimensional base. The CI chart is flat
over its radial parameter because that parameter is a nonzerodivisor.
These facts show that the nine additional charts impose no canonical
extension condition beyond regularity across the first exceptional
divisor. The inherited chart has exactly the already known old weighted
extension criterion.

Now let I_old be the generic adjoint monomial ideal

```
I_old={f : every monomial has 3*deg_eps+2*deg_W+6*deg_B+6*deg_R >=8}.
```

The first new discrepancy is `12-6-8-1=-3`, so regularity there requires
new weight at least3. The only monomials of smaller new weight are
`1,eps,W,eps^2,eps*W,W^2,R`; each has old weight below8. Therefore
`I_old` automatically satisfies this first valuation. In the inherited
chart, a monomial in I_old acquires only a nonnegative power of the new
radial coordinate, and its remaining old weight stays at least8. It thus
extends through the second weighted resolution too. This proves that
I_old is sufficient at P0, including all its finite quotient charts.

Conversely, a canonical coefficient extending through the whole local
resolution must satisfy I_old for every neighboring generic n. Its
finitely many low-old-weight coefficients are analytic functions of n;
their vanishing off n=0 forces their identical vanishing. Thus the local
adjoint ideal is exactly I_old. In particular P0 introduces no additional
restriction on the previously constructed global adjoint-jet sections.

The actual source has also been retained. In the normalized coordinates,
its initial numerator is `-q^(-3)*eps^4*B/36` times
`deps*dW*dB*dR*dn/F^2`. Its new weighted numerator degree is8, and its
ambient pullback has radial exponent7. This calculation binds the model
to the actual source and its character; it does not by itself construct
a global Gysin preimage or a certificate.
