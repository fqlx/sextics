# Fixed nonlinear ratios: the actual curve kernel

This note gives a source-retaining geometric model and a partial current. It
does not give a serving cycle, a full primitive, or an exclusion.

Use the exact constant-density chart with `u,v` held constant:

```
H0 = 1+Z^-2,  C = Z^2+u^6+v^6,
b = u/2,     D = v*(1/3+u/(2*Z)),
f = h^6+C*p^3+D*h*p+b*p+H0,
g = f_p,     q = f_h,
R = (b+D*h)*p/g^3.
```

The original nonlinear ratios are `u=Y1/(X1*Y0)` and
`v=Y2/(X1*Y0)` on `X0=1`. They are distinct from fixing two original
coordinate ratios. A primitive relative to `u,v` would directly give a
primitive of the full source, since its extra horizontal derivatives vanish
after wedging with `du dv`.

For each fixed `Z`, adjoining `w` with `w^2=p` gives the plane sextic

```
h^6+C*w^6+D*h*w^2+b*w^2+H0 = 0.
```

Its involution `w -> -w` fixes the complete root `p`, and the quotient is
precisely `f(h,p)=0`. On the smooth generic fiber this quotient has genus
four: the Newton triangle has vertices `(0,0),(6,0),(0,3)` and its four
interior lattice points are `(1,1),(2,1),(3,1),(1,2)`. A convenient basis of
holomorphic differentials is

```
dh/g, h*dh/g, h^2*dh/g, p*dh/g.
```

This identifies a rank-eight curve cohomology module retaining the actual
source. It does not assert that any part of that module is served by an
elliptic factor or by algebraic cycles. In particular, the quotient does not
remove the cubic root `p`.

The source is a specific variation of the last displayed differential.
Temporarily varying `b` independently of `H0,C,D`, implicit differentiation
on `f=0` gives

```
partial_b (p/g) = -2*(b+D*h)*p/g^3 = -2*R.
```

The actual physical derivative is not `partial_b`: `u` also changes `C`
and `D`. Those terms must remain in a source construction.

The exact first current in `first-relative-current.md` gives the full
four-form identity, with the actual chart orientation,

```
R*Omega
  = d[-p^2/(6*g*q) * dZ du dv]
    -5*p^2*h^4/q^3 * dZ dp du dv,
Omega = -(1/3)*dZ dh du dv.
```

Thus the concrete remaining constructive obligation is to integrate or
serve the last four-form, retaining its `q` poles and the entire curve
kernel. The degeneration `D=0` is the already studied support D3 and is not
a new cycle construction.
