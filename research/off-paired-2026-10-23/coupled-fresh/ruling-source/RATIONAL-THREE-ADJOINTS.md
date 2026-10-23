# Rational source and all three adjoints in inverse-root coordinates

This is an exact constructive reduction of the actual forcing. No solution
of the resulting differential equation, literal primitive or certificate is
claimed. The curve kernel and the previously recorded Cartan primitives
remain necessary throughout.

Use `i=c/e^2`, `J=d^2/e^2`, `v=e^6` and the actual physical z. On the
appropriate finite coefficient cover, set

```
T=1+z^6, k=3i z^2/(4T), A=k^2T/J, R=A-1, S=k^6/R, B=1+S,
v=z^6/(64T^4 A B),
hsrc=z^4 A/(8kT^2 Delta), Hsrc=e^(-5) hsrc.
```

Thus hsrc and v are rational in i,J,z. The sign of d is retained in the
curve kernel; using J in scalar potentials does not set that sign or drop
the kernel's d dependence.

Define rational derivations, with displayed partial derivatives taken at
fixed other members of (i,J,z), by

```
Ac=partial_i-(v_i/v_z)partial_z,
Bc=partial_J-(v_J/v_z)partial_z,
Zc=(v/v_z)partial_z,
Dc=6Zc-2i Ac-2J Bc.
```

Ac, Bc and Zc commute: equivalently they are partial_i at fixed v,
partial_J at fixed v, and v partial_v. Chain rule gives

```
partial_c=e^(-2) Ac,
partial_d=2sqrt(J)e^(-1) Bc,
partial_e[e^ell f]=e^(ell-1)(Dc+ell)f,
A0[e^ell f]=e^ell[-Zc-ell/6-J Bc]f,
B0[e^ell f]=e^ell[-Zc-ell/6]f,
T0[e^ell f]=e^ell[-Zc-Dc/2-2ell/3]f.
```

Consequently the three exact normalized adjoints of
`adjoint-reconstruction/CHI-THREE-OPERATOR-CURRENTS.md` become

```
PE*[e^(-5) f]=e^(-7) LE f,
LE=(Dc-6)(Dc-5)+Ac(Zc+Dc/2-2),

PD*[e^(-5) g]=e^(-7) LD g,
LD=4J Bc^2+2Bc+Ac(Zc+J Bc),

P3*[e^(-1) h]=e^(-7) L3 h,
L3=Ac^3+v(Zc+J Bc+1)Zc(Zc+Dc/2+1).
```

Operator products act right to left. These are not extra annihilator
assumptions: they are coordinate versions of the already proved adjoints,
with their literal current reconstruction still supplied by that file.
The actual forcing is

```
partial_e^2 Hsrc=e^(-7)(Dc-6)(Dc-5)hsrc.
```

The homogeneous cross-current of `HOMOGENEOUS-CROSS-MULTIPLIERS.md` adds
`e^(-7) F_ii(i,J)` while closing its two residue terms. Thus the source
problem can be attacked with rational functions f,g,h of i,J,z and F of
i,J; it does not require an arbitrary polynomial coefficient search in
the normalized variables.

## Exact source moment without the apparent Delta pole

Put

```
N=9i^2 z^4-16JT,
M=256T^5N+729i^6J z^12.
```

Then

```
v=64J z^2T^2N/(9i^2M),
hsrc*v_z/v=768i z^5T^3/M,
hsrc*v_z/v^2=108i^3 z^3T/(JN).
```

With w=z^2 the last expression becomes
`hsrc*v_w/v^2=54i^3 wT/(JN)`, where
`T=1+w^3,N=9i^2w^2-16JT`. This is a genuine simplification of the
inverse-root source moment: the coefficient-map branch pole Delta has
cancelled. It does not prove that its integral against the genus-four
kernel is algebraic or that a scalar density primitive serves the source.

The direct symbolic identities are checked by
`verify_rational_source_moment.py`. A rational Hermite or root-moment
reduction that also uses the full kernel operators remains open.

## Forced leading-fold moment, preserving the served N residue

In w coordinates set `P=AA*v+BB`, `AA=9i^2M`,
`BB=-64JwT^2N`. Then

```
hsrc=-3456i^3 v w^2T^3/P_w.
```

For coefficient partial derivatives at fixed w put

```
U=BB_i AA-AA_i BB, V=BB_J AA-AA_J BB,
Ccrit=(BB_w AA-AA_w BB)/T,
K=-6BB AA-2iU-2JV,
S3=U^3+BB^2(-BB AA+JV)(-4BB AA-iU-JV),
Fsrc=-3456i^3 BB w^2T^3 K^2.
```

The generic division defining Ccrit is exact and has degree 24. Matching
the source's highest fifth-order fold pole with the cubic-adjoint moment
G requires

```
G_w=Fsrc/S3 mod Ccrit.
```

An exact specialization at i=8/3,J=1 modulo 1009 proves generically that
Ccrit is squarefree, coprime to N, and coprime to S3. Both quadratic
principal symbols are also invertible modulo Ccrit at this specialization.
The generic inverse and G_w therefore have concrete rational determinant
constructions over Q(i,J); the specialized arrays are pivot witnesses,
not claimed generic coefficient lifts.

To keep the already served N residue unchanged, use the explicit Hermite
interpolation construction suggested by the source-match agent:

```
r=Fsrc S3^(-1) mod Ccrit,
H=r (N^2 Ccrit')^(-1) mod Ccrit,
G=N^2 Ccrit H.
```

Then `G_w=r mod Ccrit` and `N^2` divides G. At generic N=0 one has
v proportional to N with a nonzero unit, so the actual cubic potential
`e^(-1)G` is O(e^11) and does not reintroduce the served finite-N residue.
Analogous quadratic potentials use `e^(-5)` and remain O(e^7) with the
same N^2 condition. All other boundary and coefficient-resultant poles
must still be tracked.

`verify_fold_symbol_witness.py` independently computes and checks the
principal inverse, ordinary moment and N^2-preserving CRT moment modulo
1009. The latter's degree is forced by interpolation, not selected as a
search bound. Lower fold poles, the full rational lift and the regular
remainder are still unsolved; this is an exact construction for the
leading source term only.
