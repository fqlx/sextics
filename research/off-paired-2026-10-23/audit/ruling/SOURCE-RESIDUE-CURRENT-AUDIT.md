# Independent actual-source residue and full-current audit

The corrected source residue, the coupled residue maps, and the cubic
residue lift agree. There is also a valid all-pole proof of rational
Hermite exactness for the canonical corrected-source potentials defined
below. The newer N-only packet supplies an explicit scalar K construction,
whose compact formulas and serialized primitive derivatives are checked
below. Its compact-kernel correction remains unserved. No certificate has
been found.

`verify_actual_residue_map_fraction.py` passes 45 independent exact
Fraction groups. It does not rerun the Ore Euclidean algorithm. It checks
the physical source moment by cleared polynomial arithmetic, derives the
source and operator residue maps, checks the product-rule transports and
the exact cubic composition, and spot-checks the saved corrected-source
arrays with exact Taylor derivatives at five rational points. The result
packet is `actual-residue-map-fraction-results.json`.

## Actual source binding

The source-bearing normalized density and canonical curve are the ones
audited in `RULING-SOURCE-AUDIT.md` and `TORIC-HEAT-AUDIT.md`; they arise
from the immutable sextic with original numerator `X0^3Y0^3` and q=1.
No source-free density or a different polynomial is substituted here.

Use `i=c/e^2`, `J=d^2/e^2`, `v=e^6`, `w=z^2`, and write

```
T=1+w^3,
k=3iw/(4T), A=k^2T/J, R=A-1, S=k^6/R, B=1+S,
Delta=3RS w^3-3RS-8R w^3+R-S w^3+2S,
Hsrc=e^-5 h, h=3iw^3/(32JT^2 Delta),
N=9i^2w^2-16JT,
M=256T^5N+729i^6Jw^6,
v=64JwT^2N/(9i^2M).
```

The factorization `Hsrc=e^-5h` follows directly from the audited
`Hsrc=4T^(4/3)A^(11/6)B^(5/6)/(zk Delta)` and
`e=z/(2T^(2/3)(AB)^(1/6))`; the displayed i and J remove all fractional
powers from h and v. The actual forcing is

```
Ssrc=(D-6)(D-5)h,
partial_e^2 Hsrc=e^-7 Ssrc.                  (1)
```

For rational functions of `(i,J,w)`, let

```
Aop=partial_i at fixed(v,J),
Bop=partial_J at fixed(v,i),
Z=v partial_v=(v/v_w)partial_w,
D=6Z-2i Aop-2J Bop,
alpha(F)=F dv/v^2=F v_w dw/v^2.
```

The independent cleared-polynomial check verifies

```
alpha(h)=54i^3wT/(JN) dw.                    (2)
```

In particular the physical Delta pole cancels in this exact moment;
this cancellation is not inferred from a restricted numerical point.

## Correct forced N residue

At a generic simple root of N, v has a simple zero. Let ρ be its residue
map for the one-form alpha. Then

```
ρ(Aop F)=partial_i ρ(F), ρ(Bop F)=partial_J ρ(F),
ρ(ZF)=ρ(F),
ρ(DF)=(6-2i partial_i-2J partial_J)ρ(F).
```

The last equality is not obtained by setting Z to zero: the moment uses
`dv/v^2`, so Z acts by one on the residue coefficient.

Put `u=J/i^2`. On N=0,

```
u=9w^2/(16T),
ρ(h)=i^-1 r(u),
r=32T^3/[3w^2(2-w^3)].
```

The symbol r denotes a member of the cubic field
`Q(u)[w]/(9w^2-16u(1+w^3))`. The physical residue includes the displayed
`i^-1`. With `theta=u partial_u`, equation (1) gives

```
ρ(Ssrc)=i^-1 rTarget,
rTarget=2(theta+1)(2theta+3)r
       =4u^2 r_uu+14u r_u+6r.                (3)
```

This correction is essential. For example at `w=1,u=9/32`, r is
`256/3`, whereas rTarget is `118784`. The authoritative
`actual_Ssrc_residue` arrays are checked against (3); the separate
`h_residue` arrays are diagnostic and cannot serve (1).

## The source-carrying residue images

The full rationalized adjoints are

```
LE=(D-6)(D-5)+Aop(Z+D/2-2),
LD=4J Bop^2+2Bop+Aop(Z+J Bop),
L3=Aop^3+v(Z+J Bop+1)Z(Z+D/2+1).
```

For a residue field function, set `Eop=i partial_i+J partial_J`.
The induced maps are exactly

```
ρ LE =2Eop(2Eop-1)+partial_i(2-Eop),
ρ LD =4J partial_J^2+2partial_J+partial_i(1+J partial_J).
```

If

```
ρ(F)=2i^-1 t_u, ρ(G)=(theta+2)t,
```

the scale `i^-2` terms cancel and

```
ρ[LE(F)+LD(G)]=i^-1 L1 t,
L1=2(theta+1)[u(4-u)partial_u^2+3(2-u)partial_u]. (4)
```

The independent checker derives this cancellation as a differential
coefficient identity on an arbitrary t; it does not assume the quoted
answer from the Ore packet.

For every rational tLift there is a literal identity

```
L3(v tLift)
 =v Aop^3 tLift
  +(Z-1)[v^2(Z+J Bop+2)(Z+D/2+5)tLift].     (5)
```

It follows from `Aop(v)=Bop(v)=0`, `Z(v)=v`, `D(v)=6v`, and the
commutation of Z with `Aop,Bop,D`. It is independently checked on the
coefficient polynomial for arbitrary monomial exponents; no noncommuting
operator is moved through a coefficient without its product rule.
When `tLift=i^2 H(u)` on N,

```
ρ L3(v tLift)=partial_i^3(i^2H)=i^-1 L2 H,
L2=-4theta(1-2theta)(1-theta).                (6)
```

Root's separate arbitrary-function audit verifies the exact RIGHT
identity `L1 U+L2 V=1`. Define the canonical potentials by

```
t=U rTarget, H=V rTarget,
f=2t_u, g=(theta+2)t.
```

Equations (3)-(6) prove the N residue match for the actual source. The
independent five-point Taylor checks also verify the stored t,H,f,g arrays
and their CRT normalization against these definitions, with u differentiated
along the cubic branch. They are source-binding spot checks, not a new
global proof of the serialized arrays.

## All finite poles: an exact rational proof

There is a direct way to control every other residue without expanding
seventh derivatives. For any rational F, product rule gives literal
one-form identities

```
alpha(Aop F)=partial_i alpha(F)-d_w(F v_i/v^2),
alpha(Bop F)=partial_J alpha(F)-d_w(F v_J/v^2),
alpha(ZF)=alpha(F)+d_w(F/v).                 (7)
```

Here parameter derivatives on one-forms on the right hold w fixed.
These identities were independently checked with formal independent
symbols for F, its derivatives, and v and its derivatives. Parameter
derivatives preserve rational exactness, so their compositions control
the full LE, LD, D and source moments, including every fold pole created
by their inverse-root vector fields.

Use the polynomial-in-w representatives f,g in the cubic field, and put
`N0=N/i^2`. The actual rational lifts are

```
F=(v^2/v_w)i^-1 f N0_w/N0,
G=(v^2/v_w)g N0_w/N0.
```

Their alpha moments have finite poles only at N=0. Equation (2) gives
the same property for h. The pole loci of their parameter derivatives
still lie in N=0; all other poles introduced by the exact corrections
of (7), including folds, have zero residue.

For the cubic lift, choose the degree-at-most-two representative

```
Crt=H/(729u w^7T) modulo N0,
tLift=i^-6 wT M Crt.
```

The quotient inverses defining Crt lie in `Q(u)[w]/N0`; generically its
coefficients are rational functions of u, independent of w. Thus tLift
is a polynomial in w over `Q(i,J)`, divisible by w,T,M. Since

```
M=729i^8u w^6 modulo N0,
```

it restricts to `i^2H` on N0, as required by (6). Moreover

```
dlog v=dw/w+dlog N+2dlog T-dlog M.
```

The divisibility by w,T,M cancels every finite non-N pole of
`tLift dlog v`. Applying (5) and the logarithmic version of (7) gives

```
alpha[L3(v tLift)] =partial_i^3(tLift dlog v)
                     modulo rational exact one-forms.
```

Therefore it too has no finite residues outside N. Coefficient-field
denominators depending only on i,J do not create extra w poles on the
generic rational curve.

For the canonical corrected-source functions just defined, set

```
Rrem=Ssrc-LE(F)-LD(G)-L3(v tLift).
```

The served N residues and this all-pole argument prove every finite
residue of alpha(Rrem) vanishes. Its infinity residue is then zero by
the rational residue theorem. A rational one-form on `P^1_w` has a
rational primitive precisely when all its residues vanish. Consequently
there exists `W∈Q(i,J)(w)` with `d_w W=alpha(Rrem)`. Setting `K=vW`
gives the exact rational identity

```
Rrem=(Z-1)K.                                (8)
```

This proves rational Hermite existence for (8), not a source primitive.
It does not require any claim that the genus-four kernel is constant.

## The explicit scalar K construction

The newer primary packet
`ruling-source/adjoint-reconstruction/N-ONLY-RATIONAL-LIFT.md` gives an
explicit K using exact Hermite reduction of an N-only representative.
The correction terms are literal rational functions:

```
E_A(F)=-F v_i/v^2, E_B(F)=-F v_J/v^2, E_Z(F)=F/v,
E_D(F)=6F/v+2iF v_i/v^2+2JF v_J/v^2,
E_MN(F)=barM E_N(F)+E_M(NF).
```

The bars are the coefficient-field operators in (7), with `barZ=1`;
they commute with the w differential. Thus the recursive product formula
does retain the exact correction for each full differentiated operator.
With `Wc=v^2(Z+JBop+2)(Z+D/2+5)tLift`, put

```
Ctot=E_(D-6)(D-5)(h)-E_LE(F)-E_LD(G)
     -E_A^3(v tLift)-Wc/v.
```

If `H_N'=R_N` is the N-only representative primitive, then

```
alpha(Rrem)=d_w(H_N+Ctot), K=v(H_N+Ctot).
```

This is a specified rational construction for K, using only the hashed
source arrays, finite differentiations, and the serialized rational
Hermite coefficients. It avoids leaving an unspecified analytic
antiderivative.

The additional independent script `verify_n_only_hermite_fraction.py`
passes 13 checks. It verifies the compact split of `tLift dlogv` as
a cleared polynomial identity and reconstructs the three source
components `i^-1 r_-1+i^-2 r_-2+i^-7 r_-7` by independent Fraction
Taylor derivatives. At four exact generic `(u,w)` points, derivatives of
the supplied H_N arrays match all three source components. It imports no
primary implementation and does not rerun the primary Hermite program.

The inspected primary program performs full exact `QQ(u)[w]` derivative
checks and zero simple-remainder checks for all three components. Those
global computations have been inspected; this audit's independent array
check is explicitly a four-point check. Results are saved in
`n-only-hermite-fraction-results.json`; the checked primitive packet
SHA256 is `537c4c3a0b594e31dc45ee1d3a30e736fb3ae9ecfdf873d8382846de821076b7`.

## The full current still has a kernel defect

In normalized `(c,d,e)` coordinates,

```
Z=(c/3)partial_c+(d/6)partial_d+(e/6)partial_e,
div Z=2/3, Z(e^-7)=-(7/6)e^-7, B0=-Z.
```

Restoring the normalized toric kernel χ, one obtains

```
div[e^-7 Kχ Z]=e^-7[(Z-1/2)K χ+K Zχ],
e^-7(Z-1)K χ
 =div[e^-7 Kχ Z]+e^-7 K(B0-1/2)χ.           (9)
```

Both the divergence `2/3` and the derivative of χ are essential. Equation
(8) cannot be promoted to an absolute primitive by dropping the last
term of (9). The rational Green and fiber-Cartan currents for LE, LD
and L3 remain as in the three-operator reconstruction; their sign and
the overall normalized constant `b00^2=-1` must be restored consistently.

Thus the residue and scalar K constructions advance the actual source to
an explicit compact-kernel correction. Cancelling that correction remains open. No
Lean verification, protected CI result or acceptance is claimed.
