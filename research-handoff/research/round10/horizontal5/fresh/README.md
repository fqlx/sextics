# Horizontal residue forms and the effective-graph cone

This is constructive scratch work for the actual cyclic-triple-residual
source. It gives exact residue-closed current families and identifies a
nonrational local geometry of the source-specific effective graph. It does
not supply a proper source primitive, global H20 class, or certificate.

## General horizontal equation

Put `s=e=N1/N0`, `c=5/7`,

```
A=c*(1+e), B=L+r*e+e^3/x,
C(w,e)=w^6+A*w^3+B, u=w^3,
sigma_j=w^(3j)*dw/((T-e)*C_T), j=0,1.
```

The residues are `r0=-1/C_w`, `r1=-u/C_w`. Let `R` be the previously
audited row-basis residue connection. For two base 2-forms `gamma0,gamma1`,
the full residue-closedness equation is

```
d gamma + R^T wedge gamma=0.
```

The effective pullback is the full one:

```
dA=c*de,
dB=dL+e*dr-e^3*dx/x^2+(r+3*e^2/x)*de,
de=d(N1/N0)(L,r,x,z).
```

Physical `z=BR/Aphys` also varies with all of `(a,b,v)` and must be
differentiated. On a physical three-dimensional base, write
`gamma_j=i_(Z_j)(da db dv)`. The equation becomes

```
sum_i [partial_i Z_i + R_i^T Z_i]=0.
```

If `Z` denotes the normalized physical current used by the source compiler,
the density is `H=rho*fT`, so the actual equation instead has
`R_i^T+(partial_i log H)I`. Here

```
rho^3=m=Aphys/(3S),
fT=3*a^3*S/(2*Bphys^3*Aphys),
kappa=dlogrho=dm/(3m).
```

## Identification with a finite-cover de Rham equation

The map

```
(gamma0,gamma1) -> alpha=-(gamma0+u*gamma1)/(3*w^2*(2*u+A))
```

identifies the residue complex with the `chi` sector of ordinary de Rham
forms on the six-point graph cover `w^6+A*w^3+B=0`. It is an isomorphism
away from the usual discriminant. In the basis `(w,w^4)`, the map back to
sigma coefficients has matrix

```
T=3*[[2B,-AB],[A,2B-A^2]], det T=-9B*(A^2-4B).
```

`horizontal_forms.py` checks its exact connection gauge identity. Thus this
is the full closedness equation, not a trace projection that drops a sheet
or character. Nonexact ordinary de Rham classes on this graph cover are the
potential new residue inputs. A finite cover by itself does not establish
that such classes have the required proper holomorphic type or source image.

## Small exact horizontal currents

Without the physical rho twist, `dw wedge df` corresponds exactly to
`(dB wedge df,dA wedge df)`. To retain rational normalized physical
coefficients, use `d(rho*w) wedge df` instead. The resulting pair is

```
gamma0=(dB+6B*kappa) wedge df/fT,
gamma1=(dA+3A*kappa) wedge df/fT.
```

The second family, from `d(rho*w^4) wedge df`, is

```
gamma0=(-4B*dA-3AB*kappa) wedge df/fT,
gamma1=(4*dB-4A*dA+3*(2B-A^2)*kappa) wedge df/fT.
```

For any base functions `f,g`, replacing `df` by the product-rule expression
for `d(rho*w*f) wedge dg` or `d(rho*w^4*f) wedge dg` gives the larger exact
families saved in `horizontal_forms.pickle`. Their residue 1-form potentials
in normalized coefficients are

```
lambda_w=(f/fT)*(6B,3A)*dg,
lambda_w4=(f/fT)*(-3AB,3*(2B-A^2))*dg.
```

Exact exterior identities verify `D_res lambda=gamma` and `D_res gamma=0`,
including the full density twist. If `E` is the boundary-to-proper extension
block, flatness gives `E^T wedge gamma=-D_proper(E^T wedge lambda)`.
These are useful structured proper-current preconditioners. Because they
are exact residue classes, they do not alone establish a new Gysin image.

`physical_candidates.py` exports `candidate(point,family,f,g)` with exact
modular values and first jets of the two three-component physical current
vectors. Sixty independent physical tests pass, including the full effective
section chain rule and rho/fT twist. The universal identities are exact over Q;
these point tests separately audit the physical compiler.

## Actual nonrational cone at the effective-pencil base curve

At a transverse common zero of the reduced physical `N0,N1`, set
`U=N0`, `V=N1`, so `e=V/U`. With `w` the affine marked coordinate, the
integral generators `Z=U*w^2`, `R=U*w` satisfy

```
ZU=R^2,
Z^3+cR^3+cZRV+L*U^3+r*U^2*V+V^3/x=0.
```

These are exact equations, not just a tangent parametrization. Reduce
`R^3=RZU`; the monic leading terms are `R^2,Z^3`, giving a finite free
rank-six model with basis `(1,Z,Z^2,R,RZ,RZ^2)`. The original graph is
recovered on `U!=0` by `w=R/U`, `e=V/U`.

At the generic point of the common-zero curve, the projective leading curve
is the canonical embedding

```
[Z:R:U:V]=[W^2:Wh:h^2:T]
```

of the original genus-four weighted sextic. It is a smooth `(2,3)` complete
intersection when `x*D1*D2!=0`. Its cone is normal. Blowing up the vertex has
exceptional curve C with conormal `O_C(1)=K_C` as ordinary line bundles.
Formal functions give transverse geometric genus five:
`h1(O_C)=4`, `h1(O_C(1))=1`, and `h1(O_C(n))=0` for `n>=2`. The constant
at the first thickening lifts, so its boundary map does not remove the
one-dimensional term. This also applies to the indicated higher-order
deformation of the cone along a transverse physical curve.

Under `w -> zeta*w`, coordinates have characters `(2,1,0,0)`, the quadric
has character 2, and the cubic is invariant. Equivariant adjunction gives
`K_C=O_C(1) tensor chi`. Consequently:

```
H1(O_C):        (1,1,2),
H1(O_C(1)):     (0,0,1),
total R1(O):    (1,1,3),
```

listed by characters `(1,chi,chi^2)`. The rank-three `chi^2` defect is the
one dual to an actual-character H20 channel. Reflection independently audited
the normalization, discrepancy, formal-functions count, and character shift.

The mechanism is nonempty on a characteristic-zero component of the actual
physical graph. `transverse_point.py` finds the good point
`(a,b,v)=(41,25,1)` modulo 101, with N0=N1=0 and nonzero ab Jacobian minor 53.
All physical denominators and both curve discriminants are units. Relative
smoothness at this point lifts to characteristic zero.

## Precise global gap

The main smooth-curve indeterminacy component is cut off the boundary by
`F447=F41=0`. Their naive bidegrees on P2 x P1 are `(19,16)` and `(9,8)`.
The unsaturated complete intersection has arithmetic genus 5582; this is not
claimed to be the normalization genus. The reduced canonical pencil has
naive common line bundle `O(21,20)`, and additional boundary/common-zero
components must be tracked before using this globally.

The local rank-three defect does not yet give H20 of the entire normalized
threefold. The necessary next data are its global transitions/linearizations
along the common-zero curve and the Leray map

```
H1(base_curve,R1 pi_*O) -> H3(normalization,O).
```

Global holomorphic 2-forms require the appropriate kernel and source
projection. Certificate_search owns those twists/cohomology calculations;
reflection audits the obstruction-map direction. Off_paired owns the radial
current amplitudes `N0^-2` suggested by this cone, including the two leading
holomorphic modes from `(1,s)*dw/C_T wedge dv`.
