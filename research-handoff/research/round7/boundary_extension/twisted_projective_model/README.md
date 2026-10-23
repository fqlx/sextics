# A genuine complete-intersection compactification

This replaces the untwisted product model, whose raw equations had
codimension-two corner components. It has the same affine function field
and retains the intrinsic U->-U action.

Use the weighted projective bundle over B=(P1)^3 with Cox degrees

| coordinate | q | h | v | fiber |
|---|---:|---:|---:|---:|
| q0,q1 | 1 | 0 | 0 | 0 |
| h0,h1 | 0 | 1 | 0 | 0 |
| v0,v1 | 0 | 0 | 1 | 0 |
| U | 2 | 2 | 0 | 1 |
| t | 4 | 4 | 2 | 2 |
| z | 0 | 0 | 0 | 1 |

The three homogenized equations have degrees
`(12,12,4;6),(12,12,5;6),(12,12,6;6)`. The builder checks every monomial
and exact affine replay. E3 is monic in t³. At v=infinity the equations are

`U^4(U²+3t), 3U²t², t³`.

Thus their fiber support is the point U=t=0 rather than a whole fiber
divisor. This removes the old codimension-two components.

## Complete-intersection proof

Write E1=l*t+m, E2=n*t²+o*t+p, E3=t³+a*t+b. Here l=3U^4*v1².
Off U*v1=0, eliminating t gives

```
R12=n*m²-o*m*l+p*l²,
R13=-m³-a*m*l²+b*l³.
```

The exact finite-field computation `height_gcd_mod109.sing/.log` finds
gcd(R12,R13)=1 in characteristic109 with ell=46. Both polynomials are
homogeneous for the strictly positive weights
`(U,t,z,v1,v0,h1,h0,q1,q0)=(5,12,1,1,1,1,1,1,1)`.
Consequently this good-prime coprimality proves characteristic-zero
coprimality too: a common factor over the local coefficient DVR can be
chosen primitive and homogeneous of positive degree; its nonzero
reduction cannot become a unit. This proves height at least three off
U*v1=0.

On U=0 or v1=0, E1=B2*z^6 for a nonzero polynomial B2 independent of t,
while E3 is monic in t³. They are coprime, so adding U or v1 still gives
height at least three. Krull's bound gives height exactly three globally.
The raw Cox equations therefore form a regular sequence. This proof does
not assume that the raw CI is irreducible or normal.

## Canonical and cohomology data

The ambient canonical degree is `(-8,-8,-4;-4)`, so the raw CI dualizing
degree is `(28,28,11;14)`. For the closure of the desired open component,

```
J=(E1,E2,E3),
I=J:(q0*h0*v0*h1*(h1²-4h0²)*v1*U*z
      *(v1²-v0²)*(v1²-ell*v0²))^infinity,
omega_main = ((J:I)/J)(28,28,11;14)
```

after Cox sheafification. This linkage formula is valid here because J
really has height three. It does not give the normalization/resolution
adjoint module automatically. Full saturation/colon generators remain a
separate bounded computation in `saturate_mod109.sing`.

`cohomology.py/.json` verifies H¹(O_rawCI)=0 by Koszul/Leray. For negative
fiber degree, relative Serre duality gives

`R² pi_*O(-A;-d) = sum O(-A+(6,6,2)+i(2,2,0)+j(4,4,2))`,

where `i+2j+k=d-4`. The only possible total-degree-one Koszul term is
H⁴(O(-E123)), dimension two, represented by t^7 with base degrees
(-2,-2,+1). Its differential to H⁴(O(-E12)), also dimension two and
represented by t^4 with the same base degrees, is multiplication by
E3's monic t³. Hence that map is the identity and H¹ vanishes.

This is the raw reducible/singular CI's cohomology. The resolved main
component can still acquire irregularity through normalization and
resolution defects. Those conductor/adjoint corrections are the missing
global calculation; no global odd one-form or original certificate is
asserted here.
