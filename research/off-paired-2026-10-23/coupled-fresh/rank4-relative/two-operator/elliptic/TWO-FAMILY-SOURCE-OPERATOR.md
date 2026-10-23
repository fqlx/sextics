# Exact source operator after the Prym current

This is a verified source-carrying reduction, not a primitive. It retains all
four endpoint compact components and the background infinity-residue component.
The endpoint current and orientation are those in
`endpoint/cubic-ray/background-elliptic/first_prym_current.py`.

Put

```
D=H-1-z^6, B=-z/2,
s^2=2q^3+Bq+D, d^2=-2q^3+Bq+D,
C=q/3+z(s+d)/4, w=sd,
Delta_b=4B^6-729D^4=(z^3-108D^2)(z^3+108D^2)/16.
```

Write `e0=omega0`, `MC e0=∇C omega0`, and
`theta=(dq/d-dq/s)/12`. The actual original source satisfies, in the
literal endpoint-first frame,

```
S=dJ0+[alpha MC e0+beta e0] ^ dH ^ dq ^ dz,
J0=omega0 ^ theta ^ dz/6,
alpha=z q^3/(144s^2d^2), beta=(s^-3-d^-3)/144.
```

For A=+2 or -2 define the exact elliptic H-column

```
R_A=(6ABq^2-9ADq+4B^2)/(27AD^2+4B^3),
m_A(q)=-9AD/[2(27AD^2+4B^3)]-3ABq/(27AD^2+4B^3).
```

It obeys `∂H(dq/y_A)=m_A(q)dq/y_A+dq(R_A/y_A)` with
`y_+=s,y_-=d`. Set `Rs=R_2,Rd=R_-2,Q=Rd/d-Rs/s`. The additional literal
current

```
J2=Q omega0 ^ dH ^ dz/72
```

gives the exact remainder

```
S-d(J0+J2)=[ A0 MC e0 + B0 e0 ] ^ dH ^ dq ^ dz,
A0=alpha-C_q Q/72,
B0=[m_-2(q)/d-m_2(q)/s]/72,
C_q=1/3+z[(6q^2-z/2)/s+(-6q^2-z/2)/d]/8.
```

The `C_q` term is part of the source. Dropping it would erase the following
same-family genus-two contribution.

## Canonical character decomposition

The complete first-order endpoint operator on the remaining coefficient is

```
O_src = (A_rat + Rs/(216s)-Rd/(216d)+P4(q)/w) ∇C + B0,
A_rat = z^4(3D+qz)/(128 Delta_b),
P4(q) = [3D^2z^4/128 - Dz^5 q/256 + z^6 q^2/768
         -81D^3z q^3/16 -27D^2z^2 q^4/16]/Delta_b.
```

Thus the remainder is `O_src(omega0)^dH^dq^dz`, with exactly the
currents above already removed. The coefficient decomposition is an identity
in the full quadratic compositum, not a restriction to a fiber or a period.

The mixed character has

```
w^2=(D+Bq)^2-4q^6.
```

This is the same genus-two endpoint family at parameters `(D,B)`, so the
background part is already expressed in its finite polynomial basis
`q^j dq/w`, `j=0,1,2,3,4`. Its five source coefficients in that order are

```
[3D^2z^4/(128 Delta_b), -Dz^5/(256 Delta_b), z^6/(768 Delta_b),
 -81D^3z/(16 Delta_b), -27D^2z^2/(16 Delta_b)].
```

Rows 0,1,3,4 are the full compact rank-four basis; row 2 is the third-kind
form at the two infinities. It has constant nonzero residues and is retained.
The nonzero row 2 precludes treating the mixed contribution as merely an
exact derivative of the background third-kind form: those derivatives have
zero infinity residue. No cancellation or impossibility is asserted.

The canonical coefficient check is in
`verify_two_family_source.py`; the literal-current and elliptic-Dwork checks
are also independently encoded in the endpoint agent's `first_prym_current.py`.

## Exact source-directed background omega2 current

The mixed compact vector has a simple match to an existing connection column.
Let `Omega_j=q^j dq/w`, and write the background fixed-B derivative as

```
∂D Omega2=cD2·(Omega0,Omega1,Omega3,Omega4)+dq(R/w),
cD2=[6B^4D,-2B^5,162BD^2,-216B^2D]/Delta_b,
R=[-18B^3D^2-24B^4Dq-2B^5q^2+243D^3q^3
   -162BD^2q^4+108B^2Dq^5]/Delta_b.
```

Then the complete five-row mixed source identity is

```
P4(q)dq/w = (D/16)∂D Omega2 + lambda Omega2
            -Dz^5 Omega1/(128Delta_b)+27D^2z^2 Omega4/(16Delta_b)
            -(D/16)dq(R/w),
lambda=z^6/(768Delta_b).
```

This removes source rows 0 and 3 by a specific column match. It retains the
infinity row and the exact term, including its effect on the endpoint kernel.
For an explicit actual-current version, set

```
F=∇C omega0,
FH=∇H∇C omega0, FC=∇C^2 omega0,
o2=q^2/w,
JH=D o2 F/16, Jq=-D R F/(16w).
```

All universal endpoint derivatives in `FH,FC` precede physical pullback.
Thus the full physical derivatives are `∇Hphys F=FH+C_H FC` and
`∇qphys F=C_q FC`. The mixed four-form coefficient satisfies exactly

```
(P4(q)/w)F = ∇Hphys JH + ∇qphys Jq + Rem,
Rem=[(lambda-1/16)q^2/w-Dz^5q/(128Delta_b w)
     +27D^2z^2q^4/(16Delta_b w)]F
    -Dq^2(FH+C_H FC)/(16w)+D R C_q FC/(16w).
```

In the literal `omega-first,dH,dq,dz` frame the actual added three-form is

```
-Dq^2 F ^ dq ^ dz/(16w)-D R F ^ dH ^ dz/(16w).
```

Both `FH` and `FC` are full four-component compact vectors obtained from the
verified endpoint connection: `(∂H MC+MH MC)e0` and
`(∂C MC+MC^2)e0`. The displayed `C_H,C_q` terms are retained, so this is a
coupled physical current, not a primitive on a fixed background fiber.
`background_omega2_source_current.py` verifies the exact Dwork polynomial,
the source column match, and the full endpoint Leibniz remainder.
The actual four coefficients, in compact order `(0,1,3,4)`, are saved in
`endpoint-source-current-vectors.json`; for example
`F=(-4C^5,243H^3,-108C^2H,144C^3)/(4C^6-729H^4)`.
The same file includes all four entries of `FH,FC`, and the two orders of
the mixed H,C derivative were checked equal exactly.

## A genuine H,q,z,p current for the entire mixed vector

The coefficients of `P4` have weights `2-j` under
`Epar=3D∂D+2z∂z`, while `Omega_j` has weight `j-2` after including
the `q∂q` fiber scaling. Consequently **every actual source row** has
background weight zero. In particular the Omega1 source coefficient has
weight +1; dividing a raw row weight would give the wrong resonance test.
For `N=P4(q)/w`, the exact scalar identity is

```
Epar(N)=-∂q(qN).
```

In physical `(H,q,z)` coordinates the parameter Euler vector has
`Hdot=3D+12z^6`, `qdot=0`, `zdot=2z`. After adding the fiber `q∂q`, its
actual endpoint parameter velocities are

```
Hdot=3H+(9z^6-3),
Cdot=2C+(-q/3+3za/4), a=(s+d)/2.
```

The endpoint derivative `F=∇C omega0` has universal weight -4, with the
literal exact transgression

```
(3H∇H+2C∇C)F=-4F-dp(tF),
tF=-p^2(H+Cp)/Z^3.
```

For this literal formula, `F=-p(H+Cp)dp/Z^3`; its full compact vector is
the `F` in `endpoint-source-current-vectors.json`, with the canonical
Dwork exact correction understood when converting between the literal
derivative and the reduced compact basis. The current below is written
using the literal derivative, so its displayed fiber correction is explicit.

This supplies the following actual source-directed current, with no
parameter held fixed. In the literal endpoint-first orientation put

```
K=-(3D+12z^6)N F ^ dq ^ dz
  +qN F ^ dH ^ dz
  -2zN F ^ dH ^ dq
  +N tF dH ^ dq ^ dz.
```

Then exactly

```
N F ^ dH ^ dq ^ dz
 =dK-N[(9z^6-3)FH+(-q/3+3za/4)FC] ^ dH ^ dq ^ dz.
```

Thus the full source-bearing operator
`1+(9z^6-3)∇H+(-q/3+3za/4)∇C`, applied to `F`, is rationally exact after
multiplication by the *whole* `N`. This retains all five background rows
at once, all four compact endpoint rows, all physical H,q,z directions,
and the explicit fiber primitive. The two displayed defect derivatives
remain unintegrated; no inverse of this operator is assumed.
`full_mixed_euler_current.py` checks its source homogeneity, actual physical
endpoint velocities, the literal fiber transgression, and all four compact
Euler rows exactly.

## A distinct actual H-current

There is also a source-carrying H-current useful before the elliptic GM
reduction. Let `U=d-s` and `f=(1/d-1/s)/12`, so at fixed `(q,z)`, `U_H=6f`.
All endpoint coefficient derivatives below are taken at fixed universal
parameters `(H,C)` before pullback. The full physical H-connection is
`D_H^phys=∂H+C_H∂C+MH+C_H MC`, with `C_H=z(1/s+1/d)/8`.
Then

```
-f MH e0/6 = D_H^phys[-U MH e0/36] + U Q_H e0/36,
Q_H=∂H MH+MH^2+C_H(∂C MH+MC MH).
```

This is a full four-component covariant divergence identity, including the
physical `C_H` correction. It does not solve its displayed remainder and is
not a one-flow restriction. Either this identity or `J0+J2` may be used as an
initial partial current; they must not be subtracted twice.
