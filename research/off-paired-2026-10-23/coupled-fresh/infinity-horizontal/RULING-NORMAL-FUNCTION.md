# Explicit ruling differential for the source-carrying canonical family

No primitive or Gysin proof has yet been established. The explicit ruling
generator below now has source-specific derivative identities in
`../ruling-source/SHEAR-SOURCE-IDENTITY.md` and
`RATIONAL-RULING-TRACE.md`. The independent toric point-pair generator and
its literal source operators are in `TORIC-POINT-PAIR.md`.

## Canonical family and actual source

Use a=x³,b=y³,q=xy,U=u³,V=v³,p=uv on X0=1,z=Y1. The quotient equations are

```
ab=q³, UV=p³,
a²+b²+U²+V²+1+z⁶+zq/2+zap/2+qp/3=0.
```

Use varying ratios U=r a,V=s b,p=kq, with rs=k³. This gives the canonical
curve `C1=ab t−q³=0,Q=0` in P³(a,b,q,t), where

```
Q=(1+r²)a²+(1+s²)b²+(k/3)q²
  +(zk/2)aq+(z/2)qt+(1+z⁶)t².
```

These ratios remain variables of the base. This does not assert a relative
primitive after fixing two original-coordinate ratios.

The actual physical source volume transforms as

```
y³ dx∧dy∧du∧dv∧dz
 =bq/(9ar) da∧dq∧dr∧dk∧dz.
```

Choose the residue orientation of C1 so that its affine canonical two-form
is `da∧dq/a`. With that orientation the numerator is `bq`, or homogeneously
`bqt` in `bqt Omega/(C1 Q²)`. Thus it is the negative qt-coefficient
variation of the canonical curve one-form with numerator b:

```
eta_b=Res[b Omega/(C1 Q)],
source_qt=−nabla_E(eta_b), E=coefficient(qt).
```

The independent E direction is an auxiliary universal-quadric direction.
Its restriction to the actual three-parameter coefficient locus must be
restored. `canonical_qt_transport.py` gives an exact tangent/torus lift and
retains its nonzero lower-pole correction. No fixed-denominator search has
been performed here.

## Ruling third-kind generator

For the universal affine quadric write

```
Q=Aa²+Bb²+Cq²+Daq+Eq+T,
Cp=C−D²/(4A),
X=a+Dq/(2A), Y=q+E/(2Cp),
rho²=(E²/(4Cp)−T)/B,
lambda²=−A/Cp,
c0²=−A/B.
```

Work generically on A B Cp rho≠0 and a finite algebraic coefficient cover
choosing rho,lambda,c0. The norm cubic remains C1=ab−q³.
On Q the following relative one-form is a literal primitive:

```
beta0=(X dY−Y dX)/(2B(b+rho)),
d_rel beta0=da∧dq/(2Bb).
```

Define

```
beta=(2lambda Cp/rho) beta0
     =−(b−rho)/(2rho) d_rel log[(Y−lambda X)/(Y+lambda X)].
```

Its finite poles are the two ruling lines
`b=−rho,Y−lambda X=0` and `b=−rho,Y+lambda X=0`.
Their intersections with C1 are degree-three divisors D+ and D−, with
residues +1 and −1. Their divisor-class difference is the ruling section
`nu=L+−L−` of the relative Jacobian.

Infinity contributes additional residues, which cannot be dropped. The two
points at infinity are `(a:b:q:t)=(1:±c0:0:0)`. Put

```
J=a Q_a−b Q_b,
omega_inf=−(2A/c0) q²dq/J,
c_inf=3lambda E/(2B rho c0),
beta_hat=beta−c_inf omega_inf.
```

The form omega_inf has residues +1,−1 at these two points and no other
poles on a generic smooth fiber. Beta has infinity residues +c_inf,−c_inf.
Therefore beta_hat has precisely the fixed ruling residues D+−D− and zero
infinity residues. It still has third-order second-kind poles at infinity;
in particular it is not literally a differential with only simple poles.
It represents the ruling point-pair class together with this retained
second-kind data, after the stated algebraic cover. No logarithmic
coefficient is used: `d_rel log` abbreviates the rational logarithmic derivative.

## Literal parameter derivatives

On the canonical curve, use q as a local coordinate. Then

```
a_q=(−a Q_q−3q² Q_b)/J,
b_q=( b Q_q+3q² Q_a)/J.
```

For the universal qt coefficient E, holding q fixed gives

```
a_E=−a q/J, b_E=b q/J,
rho_E=E/(4B Cp rho), lambda_E=c0_E=0.
```

These derivations preserve both equations. In the first expression for beta
use

```
X dY−Y dX
 =[a−DE/(4A Cp)−(q+E/(2Cp))a_q]dq.
```

Consequently the actual literal compact variation is
`nabla_E(beta_hat)=D_E(coefficient(beta_hat))dq`; moving-pole second-kind
terms are retained. Its residues vanish because the complete ruling and
infinity residue corrections are fixed. It belongs to the full rank-eight
compact de Rham module of the genus-four curve. Exact shear and centered-E
source identities are now established in the linked follow-up files,
including actual-base lifts and nonzero adjoint remainders. Cancelling
those remainders, with all mixed derivatives, remains open.

Ten symbolic groups in `verify_ruling_third_kind.py` check the primitive,
the finite residue normalization, the actual tangent derivations, and both
infinity residue signs. The infinity proof uses the projective local chart
`a=1,q=u,t=u³/b(u)` before returning to affine coordinates.
