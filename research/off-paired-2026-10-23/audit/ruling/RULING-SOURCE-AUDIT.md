# Independent audit of the ruling source identities

The universal ruling identities and the physical source normalization check out.
No certificate has been found. Restoring the actual three-parameter base,
including its density divergence and the resulting lower-pole sources, remains
a separate obligation.

`verify_ruling_fraction.py` passes 48 groups using Python standard-library
`Fraction` coefficient arithmetic, rational quotient arithmetic, and an
independent Laurent calculation at infinity. It imports only the earlier
independent sparse-polynomial utilities in `audit/`, not the primary ruling
generator or its checker. Results are in `ruling-fraction-results.json`.

The inspected primary sources are
`coupled-fresh/infinity-horizontal/RULING-NORMAL-FUNCTION.md` and
`coupled-fresh/ruling-source/SHEAR-SOURCE-IDENTITY.md`.

## The actual source, including orientation

On `X0=1` use `(x,y,z,u,v)=(X1,Y0,Y1,X2,Y2)` and

```
a=x^3, b=y^3, q=xy, r=u^3/x^3, k=uv/(xy), s=v^3/y^3;
rs=k^3.
```

The target is exactly the current record's `F,A,q`, parsed with integer AST
nodes and exact rational arithmetic. In particular its source is `A=y^3` and
`q=1`; the quadric below substitutes to the immutable polynomial `F` exactly.
The independent earlier target-binding audit also checks mathematical equality
of the current and preserved original records.

```
A=1+r^2, B=1+s^2, C=k/3, D=zk/2, E=z/2, T=1+z^6,
Q=Aa^2+Bb^2+Cq^2+Daq+Eq+T,
C1=ab-q^3.
```

Here `A` in the universal quadric denotes a coefficient, not the original
target numerator. The Jacobian in the displayed coordinate orders is

```
det ∂(a,q,r,k)/∂(x,y,u,v)=+9ar/q,
y^3 dx∧dy∧du∧dv∧dz
 = bq/(9ar) da∧dq∧dr∧dk∧dz.
```

Choose the `C1` residue orientation induced by ambient order `da∧dq∧db`;
it gives `da∧dq/a`. The fiber numerator is therefore `bq`, or `bqt` in
the homogeneous expression `bqt Ω/(C1 Q^2)`. The physical outer density
`dr∧dk∧dz/(9r)` must be retained.

Let `J=a Q_a-b Q_b=2Aa^2+Daq-2Bb^2`. For
`η_b=b dq/J`, the literal, `q`-fixed parameter derivations give

```
(a_E,b_E)=(-aq,bq)/J, (a_T,b_T)=(-a,b)/J,
τ_source=-∇E η_b=-∇T(q η_b)
 =-2bq(3Aa^2+Daq+Bb^2)dq/J^3.                 (1)
```

The same expression follows independently by taking the double-`Q` residue
of the actual numerator. In homogeneous notation the second equality uses
`q_aff=q/t` and `Q_T=t^2`, hence `b q_aff Q_T=bqt`.

## Literal differential and all residues

Set

```
Cp=C-D^2/(4A), X=a+Dq/(2A), Y=q+E/(2Cp),
ρ^2=(E^2/(4Cp)-T)/B, λ^2=-A/Cp, c0^2=-A/B.
```

On the centered quadric, independently checking its two coordinate
derivatives gives

```
β0=(X dY-Y dX)/(2B(b+ρ)),
d_rel β0=da∧dq/(2Bb),
β=(2λCp/ρ)β0
 =-(b-ρ)/(2ρ) d_rel log[(Y-λX)/(Y+λX)].
```

The logarithm abbreviates a rational logarithmic derivative. At `b=-ρ`,
the numerator ruling has residue `+1` and the denominator ruling residue
`-1`; at `b=+ρ` their apparent logarithmic poles cancel. Each ruling meets
the norm cubic in a divisor of degree three on a generic fiber.

For the two infinities `(1:±c0:0:0)`, let

```
ω_inf=-(2A/c0)q^2dq/J,
c_inf=3λE/(2Bρc0), βhat=β-c_inf ω_inf.
```

The residues of `ω_inf` are `(+1,-1)` and those of `β` are
`(+c_inf,-c_inf)`. These signs agree with the primary computation.

There is a necessary precision: **βhat still has third-order second-kind
poles at infinity.** In the projective chart `a=1,q=u,t=u^3/b(u)`, writing
`b(0)=b0=±c0`, the independent Laurent calculation gives

```
β = [λCp/(Bρ)] u^-3 du
    +[3λE/(2Bρb0)] u^-1 du + regular,
```

with no `u^-2` term. The infinity correction cancels the residue, not the
`u^-3` principal part. Thus βhat carries the ruling third-kind residue
class together with essential second-kind data. It is not literally a
differential having only simple poles on the ruling divisors. This does not
invalidate a compact parameter derivative, but the retained data must be
included in that derivative.

## The normalized shear and its exact term

Use `S=∂D+(D/(2A))∂C`. It keeps
`A,B,Cp,E,T,λ,ρ,c0,c_inf` fixed. On the actual norm cubic at fixed `q`,

```
Sa=-aqX/J, Sb=bqX/J,
SX=q/(2A)-aqX/J=-Bb^2q/(AJ), SY=0.
```

These preserve both curve equations with the required parameter variation
`SQ=qX`. The literal identity is

```
∇S β = -[λCp/(Aρ)]q η_b+d_q F_S,
F_S=λCp·Y·b^2q/[AρJ(b+ρ)].                   (2)
```

This is also a short independent proof of the identity. Since the centered
quadric is fixed by `S`, Cartan's formula applies to its above tangent lift.
The independently checked `d_rel β=λCp dX∧dY/(Bρb)` gives
`ι_S d_rel β=-λCp bq dq/(AρJ)`, while
`ι_S β=F_S`. Both coefficient identities were checked without a curve
relation after clearing their displayed denominators. Thus (2) is an
equality of rational differential forms, including the exact moving-pole
term, not only an equality of compact classes.

The normalized form obeys the complete identity

```
∇S βhat=-[λCp/(Aρ)]q η_b+d_q F_S-c_inf∇S ω_inf. (3)
```

The last term cannot be discarded. The shear fixes its normalizer but does
not fix `ω_inf`.

For an explicit mixed-parameter formula set

```
h=Aρ/(λCp), d=3AE/(2BCp c0)=h c_inf.
```

Then `∂T h=-A/(2BλCpρ)` is nonzero, while `∂T d=0`. The complete
consequence of (1) and (3) is

```
τ_source=∇T(h∇S βhat)+d∇T∇S ω_inf
         -d_q[∇T(h F_S)].                    (4)
```

The `T` derivative in its first term acts on `h` as well. Cover extensions
are separable in characteristic zero, so the `q`-fixed coefficient
derivations commute and the displayed fiber-exact correction is well
defined.

## The normalized translation, including both infinity scalar terms

The further direction

```
V=∂E+[E/(2Cp)]∂T
```

keeps `A,B,Cp,D,ρ,λ,c0` fixed and varies `Y` by `1/(2Cp)`.
Its `q`-fixed lift is

```
Va=-aY/J, Vb=bY/J, VX=Va, VY=1/(2Cp).
```

The independent Cartan calculation, checked after clearing denominators,
gives the literal identity

```
∇V β=d_q F_E+(λ/ρ)[δ η_b+3q^2dq/J],
δ=D/(2A),
F_E=λ[XJ+2Cp aY^2]/[2BρJ(b+ρ)].             (5)
```

The exact potential is the contraction `ι_V β`. The contraction of
`d_rel β` supplies the two displayed compact/third-kind columns. No
derivative restricted prematurely to a special fiber is used.

There are two terms when differentiating `c_inf ω_inf`: its scalar
derivative and the derivative of the differential. Explicitly,

```
V(c_inf)=3λ/(2Bρc0),
[V(c_inf)]ω_inf=+(3λ/ρ)q^2dq/J,
∇V βhat=d_q F_E+(λδ/ρ)η_b-c_inf∇V ω_inf.   (6)
```

The positive sign in the middle equality follows from `c0^2=-A/B`.
Subtracting that product cancels the `q^2` term of (5); the final
`-c_inf∇V ω_inf` still remains. `V(c_inf)` must not be written as the
plain `∂E(c_inf)` at fixed `T`: the latter also differentiates `ρ`.
The checker verifies this chain-rule distinction explicitly.

These relations yield a second-order relation with all infinity columns
and coefficient derivatives visible. On `δ≠0` put

```
u=ρ/(λδ), e=3E/(2Bδc0), h=Aρ/(λCp), d=3AE/(2BCp c0).
```

Using `∇Eη_b=∇T(qη_b)`, equations (3) and (6) imply

```
∇E(u∇V βhat+e∇V ω_inf)
 +∇T(h∇S βhat+d∇S ω_inf)
 =d_q[∇E(u F_E)+∇T(h F_S)].                 (7)
```

This is not a homogeneous annihilator of βhat alone after deleting the
infinity columns. It does give an exact rational universal relation,
including its fiber-exact potential. Its physical restoration is still
subject to the outer-density calculation below.

## Independent physical lift and density spot audit

The separate `verify_actual_lifts_fraction.py` passes 85 groups at five
exact points of `k^6=RS`, with independent second-order Taylor jets in
`R,S,z`. It never imports or executes the primary script. It reconstructs
the `T`, normalized-shear, `E`, and normalized-translation lifts by a
six-by-six linear solve from the six physical coefficient equations

```
VQ=P+αQ-X_tor Q,
X_tor=u(a∂a-b∂b)+v(a∂a+b∂b+(2/3)q∂q).
```

All six submitted lift components agree through second order at those
points. The original density transforms with the positive Jacobian as

```
R=r^2, S=k^6/r^2,
dr∧dk∧dz/(9r)=dR∧dS∧dz/(108k^5),
div_μ V=∂R VR+∂S VS+∂z Vz-(5/6)(VR/R+VS/S).
```

The submitted `M_T=div_μ VT+c_T`, its first derivatives, and
`h^2=A[T-E^2/(4Cp)]/(B Cp)` also agree. For the `T` lift,
`c_T=-α-u+7v/3=2v`.

There is an explicit sign convention discrepancy between the older
primary JSON field and the source formula in the source agent's note.
With source (1), the first integration by parts leaves `M_T qη_b`.
The shear relation `qη_b=-h∇Sβ+fiber-exact` therefore leaves

```
+div_μ(h M_T VD) β,
g/h=VD(M_T)+M_T div_μ VD+(M_T/2)VD(log h^2). (8)
```

The older primary JSON field `remaining_beta_coefficient_over_h` stores
the negative of (8). At `R=S=z=k=1`, `M_T=-13/9`, (8) is `-241/9`,
and that JSON stores `+241/9`. Both signs are nonzero; the sign matters
when assembling an actual primitive. The source agent confirmed the
positive convention (8), and its newer
`ruling-source/physical-source-adjoints.json` uses `-241/9` consistently.
This audit records the convention rather than silently changing another
agent's file.

The newer source packet's `E/W` family was also checked. Its coefficient
targets are `P=∂E Q=q` and `P=VQ=q+E/(2Cp)`, respectively. For the
plain `E` lift,

```
c_E=-α-u+5v/3, h_E=div_μ VE_plain+c_E,
m=2Cp/D=κ_E/κ_S,
g_E/h=-{VW(m h_E)+(m h_E)div_μ VW
        +(m h_E/2)VW(log h^2)}.              (9)
```

At `R=S=z=k=1`, `h_E=-10/3` and (9) is `-3382/9`, agreeing with the
newer JSON. All four lifts, `h_E` and its first derivatives, `m`, and
both residuals match at the five points. This checks the finite β
coefficient; its infinity companions are still required.

The five-point checks are an independent local verification, not a global
polynomial identity proof for the submitted closed expressions. The lift
matrix derivation and the density formula are explicit above; no new
global obstruction is asserted. Detailed exact values are saved in
`actual-lifts-fraction-results.json`.

## Remaining obligation

Equations (1)-(7) are positive source-carrying universal identities. They
are not a physical primitive by themselves: the universal directions must
be restored to the actual coefficient locus, and integrations by parts
must include the physical outer density and every resulting lower-pole
term. The physical-adjoint computation retains a nonzero residual
multiple of β, confirmed at the five exact points with the sign convention
just stated. That residual is not an obstruction to other full currents.
No Lean proof, protected CI result, or acceptance follows from this
calculation.
