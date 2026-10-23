# Exact cubic-ray source on the elliptic companion

This is a source audit and a constructive interface, not a certificate.
The accompanying `cubic-ray-companion-source.py` checks the algebraic identities.

Set `X0=1`, `X1=x`, `X2=a`, and `(Y0,Y1,Y2)=(y,yu,yv)`.
With `s=y²`, the immutable target becomes

```
f(s) = H+B*s+C*s³,
H = 1+x⁶+a⁶,
C = 1+u⁶+v⁶,
B = xu/2+x³auv/2+xav/3.
```

Write `Omega4=dx∧da∧du∧dv` and use the order `Omega4∧ds`.
The actual target fiveform is

```
alpha = s²/(2f²) Omega4∧ds.
```

The factor is fixed by the Jacobian `dY0 dY1 dY2=y²dy du dv`:
`y³*y²dy=s²ds/2`. In particular no arbitrary density is being substituted.
There is an actual initial primitive and exact remainder:

```
alpha = d[-Omega4/(6C f)] - B/(6C f²) Omega4∧ds.
```

The first term is exact because `d(C⁻¹)` wedges to zero with `Omega4`.
At `B=0` this already solves the source. The given target has nonzero `B`.
For the `f` normal coordinate the remaining degree-four density is

```
R Omega4 = [B s/(3Cs²+B)³] Omega4
         = [-B/(6C) * s_HH] Omega4,
s_H=-1/(3Cs²+B),  s_HH=-6Cs/(3Cs²+B)³.
```

This is the full second normal residue of the original source, with the
orientation `df` after `Omega4`. It is the source which must be carried.

## A discriminant-denominator first current

The cubic also admits the complete Hermite reduction

```
delta = 4B³+27H²C,
Q = (Bs-3H)(2Bs+3H)/(2delta),
T = B(Bs-3H)/delta,
s²/(2f²) = d_s(Q/f) + T/f.
```

It produces an actual rational initial primitive `(Q/f)Omega4` with only
the discriminant as its extra denominator. Its nonzero remainder is the
simple physical pole `(T/f)Omega4∧ds`; it is not discarded. On the actual
physical hypersurface,

```
delta = f_s²(4B+3Cs²),
T = Bs/f_s²,
T/f_s = R.
```

Thus the first current preserves exactly the same remaining degree-four
source. This may be used with the rank-two finite cubic connection without
introducing an elliptic square-root extension.

## The rational pole on the companion

Use `E=w²-f(s)` and ambient order `Omega4∧ds∧dw`.
The second normal residue of `b/E²` in the `w` normal is

```
R2(b)=b_w/(4w²)-b/(4w³).
```

Consequently the actual source is represented by

```
b=-s²/w,
R2(b)=s²/(2w⁴).
```

After the initial vertical primitive one may instead use
`b_reduced=B/(3Cw)`, whose residue is `-B/(6Cw⁴)`.
Both retain an actual `w=0` pole. Replacing it by a polynomial expression
using the equation only returns the source:

```
b_tilde=-s²*w/f,
R2(b_tilde)=0,
b-b_tilde = E*s²/(w*f).
```

The first normal residue of the correction is
`s²/(2w² f)=s²/(2f²)`. Thus this replacement is a coefficient-one
self-cycle, not a source primitive. The corresponding statement for the
reduced source follows by the same calculation.

With `r=Cs` and `W=Cw`, the elliptic equation is

```
W²=r³+BC*r+HC²,
j=6912 B³/(4B³+27H²C).
```

The `j` invariant varies for the given `H,B,C`. A contraction theorem for a
fixed Fermat elliptic curve therefore needs an additional construction and
cannot be applied by changing the equation's appearance.

## Curve-family obligation

The cone scaling

```
(X,Y,s,w) -> (lambda X,mu Y,lambda² mu⁻² s,lambda³ w)
```

allows `s=w=1` after finite extension on the open `sw!=0`. Its equation is
the level sextic `F(X,Y)=1`, compactifying to a Fano fivefold of degree six
in `P6`. This gauge uses inverse powers of `w`. It removes the entire
physical branch `w=0`, so it supplies no normal transport of `R Omega4`
there. Its ordinary second-normal polynomial-density theorem also concerns
a fiveform on that fivefold, while the physical normal source has degree
four. A new identity is needed to pass between them.

One possible useful input is a family for the actual companion together
with its actual rational numerator, its normal jets, and the correction at
every zero of `w` along the curve. A generic zero cannot simply be erased:
if `w=t^k`, pulling back a logarithmic term gives
`dw/w=k dt/t`; its residue is the transported degree-four source on the
branch. A polynomial integration argument must prove that these residue
forms have rational primitives, or supply a translated-pole identity and
its infinity correction which cancels them. Establishing that identity for
the specific `R` remains open here.

## A full-kernel symmetry quotient

The action `a -> zeta*a, v -> zeta^-1*v`, for `zeta^6=1`, fixes `H,B,C`
and the actual fourform density. Put `k=av,t=a^6`. In the indicated order,

```
Omega4 = dx∧du∧dk∧dt/(6t),
H=1+x⁶+t,
C=1+u⁶+k⁶/t,
B=xu/2+x³uk/2+xk/3.
```

This quotient retains the entire cubic kernel; its coefficient `B` is
independent of `t`. Writing

```
G=t²+[1+x⁶+Bs+(1+u⁶)s³]t+k⁶s³,
alpha=t*s²/(12G²) dx∧du∧dk∧dt∧ds
```

gives another exact physical source interface. The quadratic discriminant
in `t` has degree six in `s`, so its genus-two companion is closely related
to the earlier endpoint chart. The quotient does not by itself provide
the remaining primitive.
