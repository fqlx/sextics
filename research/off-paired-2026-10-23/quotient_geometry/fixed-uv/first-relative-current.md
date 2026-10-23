# Actual relative current on the fixed-(u,v) surface

This is a constructive source interface, not a primitive of the whole source
or a certificate. It makes no Picard, genus, or nonexistence claim.

Work over the constant field `C(u,v)` and use the exact constant-density
chart from `endpoint/cubic-ray/poisson/CONSTANT-DENSITY-CHART.md`. Put

```
H0 = 1 + Z^-2,
D  = v*(1/3 + u/(2*Z)),
C  = Z^2 + u^6 + v^6,
B  = u/2 + D*h,
f  = H0 + h^6 + B*p + C*p^3,
g  = f_p = B + 3*C*p^2,
q  = f_h = 6*h^5 + D*p.
```

The surface is `f=0`, and the complete actual relative source is

```
R dZ dh,    R=B*p/g^3.
```

All differentials below are relative to `u,v`. On the opens where the
displayed denominators are invertible, the rational one-form

```
eta = p^2/(2*g*q) dZ
```

satisfies the exact identity on `f=0`

```
d eta = [ R + 15*p^2*h^4/(g*q^2) ] dZ dh.
```

Thus the remaining source, with its sign fixed, is

```
R dZ dh = d eta - 15*p^2*h^4/(g*q^2) dZ dh
         = d eta + 15*p^2*h^4/q^3 dZ dp.
```

The second equality uses `q dh = -f_Z dZ - g dp`. In particular it retains
the entire cubic root `p`. In coordinates `(Z,p)`, this remaining form is
regular at a generic `g=0` branch where `q` is nonzero. The remaining `q`
poles have not been integrated.

For verification in coordinates `(Z,p)`, the actual surface derivative is

```
partial_p^S = partial_p - (g/q)*partial_h.
```

For `A=p^2/(2*g*q)`, direct differentiation gives

```
partial_p^S A = B*p/(g^2*q) + 15*p^2*h^4/q^3.
```

The two mixed `D` terms cancel because `B_h=q_p=D`. This is the source of
the simple residual; dropping the variation of `h` would give the wrong
identity.

On the branch divisor `q=0`, assuming `D` nonzero, one has

```
p = -6*h^5/D,
f|_(q=0) = H0 - 5*h^6 - 3*u*h^5/D - 216*C*h^15/D^3.
```

This last equation is only an exact model for the remaining pole divisor.
No source-carrying CM or elliptic correspondence of this moving curve has
been constructed. The special equation `D=0` is the already studied D3
support and supplies no new support argument.

The full four-form is obtained by wedging this identity with
`-du dv/3`, in the same order as the exact chart volume. A primitive of
the displayed residual would therefore finish this particular relative
route and could be traced down using the existing degree-six cover and
cubic-ray source interface.

`verify_first_relative_current.py` checks the implicit-derivative identity,
its equivalent `(Z,h)` coefficient, and the pole-divisor equation by exact
symbolic rational arithmetic.
