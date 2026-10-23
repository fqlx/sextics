# The actual finite residue has an explicit current

The finite Pa residue of the constructed K is now served by a rational
two-current on the full normalized base. No integration ansatz, degree
bound or new existence assumption is needed. This does not serve the
remaining compact genus-four source.

Use the positive Ssrc convention from `N-ONLY-RATIONAL-LIFT.md`. Write

```
H=Hsrc=e^-5 hsrc,
f=e^-5 F, g=e^-5 G, h=e^-1 Hpot,
M=e^-7 K, Z=-B0,
mu=dc∧dd∧de.
```

The scalar construction supplies the literal actual-source identity

```
H_ee-PE* f-PD* g-P3* h=e^-7(Z-1)K.
```

All these are the actual hashed source and potentials, rather than the
undifferentiated hsrc residue. The original target uses the opposite
overall sign after source integration by parts.

## Full-base primitive

The normalized operators PE, PD, P3 all kill the constant function 1.
For P3 this uses its outer A0 factor: it kills the constant -1/4.
Specialize the already verified Green vectors to the constant residue:

```
BE=-f_e partial_e+(T0 f-4f/3) partial_c,
BD=-g_d partial_d+(A0 g-5g/6) partial_c,
Astarh=-A0 h+7h/6,
BstarAstarh=-B0(Astarh)+Astarh/6,
B3=-(h/4)A0+(Astarh/2)B0+BstarAstarh T0-h_cc partial_c,
V=H_e partial_e+BE+BD+B3.
```

The Green identities give

```
div V=H_ee-PE* f-PD* g-P3* h=e^-7(Z-1)K.
```

Since div Z=2/3 and Z(e^-7)=-7e^-7/6, one also has

```
div(M Z)=e^-7(Z-1)K+M/2.
W=V-M Z,
div W=-M/2.
```

On the physical finite sheet, the root's quadric reduction gives

```
M mu=-(K/3)di∧dj∧dhbase, hbase=e^-3.
```

Consequently the actual Pa residue three-form and its explicit primitive
are

```
rho_Pa=±sqrt(-1) K dhbase∧di∧dj/6
      =∓sqrt(-1)(M/2)mu,
B_Pa=±sqrt(-1) contraction(W,mu),
d B_Pa=rho_Pa.
```

This is an equality of full three-base forms. A primitive restricted to
the w direction need not exist; the c,d,e, or equivalently i,j,w,
derivatives in W are essential. It is also consistent with the original
source having zero Pa residue: the residue of zeta is the fixed constant
±sqrt(-1), while its e derivatives have zero residue.

## Equivalent compact source

The full curve-valued correction can now be transferred without any
third-kind companion:

```
M(B0-1/2)zeta=div(W zeta)-V(zeta).
```

The remaining first derivatives are literal rational curve identities,
not just their cohomology classes:

```
zeta_c=bq dq/Jcurve,
zeta_d=q^3 dq/Jcurve,
zeta_e=b dq/Jcurve.
```

All have zero finite and infinity residues. Thus the only remaining source
in this reconstruction is compact:

```
-(V_c bq+V_d q^3+V_e b)dq/Jcurve ∧mu.
```

This is an equivalent source interface; it is not a new compact exactness
theorem. Setting the three potentials to zero reduces it to the original
first source integration by parts. In particular, one must not infer that
the scalar Hermite success has automatically integrated these compact
components.

## Rational descent for the rank-eight connection

Set i=c/e^2, Jpar=d^2/e^2=j^2, v=e^6. Let A=partial_i,
B=partial_Jpar, Z=v partial_v, D=6Z-2iA-2Jpar B, and

```
U=(Z+Jpar B+1)Hpot, UZ=Z U,
Cc=(-Z-D/2+2)F-(Z+Jpar B)G-A^2 Hpot
   +i v(Hpot/12-U/6-UZ/3),
Cd=-2j B G+j v(Hpot/6-U/12-UZ/6),
Ce=(D-5)(hsrc-F)+v(Hpot/24-U/12-2UZ/3).
```

Then V_c=e^-5 Cc, V_d=e^-6 Cd, V_e=e^-6 Ce. In the deck-invariant
compact basis beta_bq=e^5 bq dq/Jcurve,
beta_q3=e^4 q^3 dq/Jcurve, beta_b=e^4 b dq/Jcurve, and with
the actual volume di∧dJpar∧dw, the source is

```
-v_w/(12j v^2) * [Cc beta_bq+Cd beta_q3+Ce beta_b].
```

The other five compact basis entries are zero in this source interface.
The generic rank-eight connection must still serve this complete source
or an equivalent source obtained by the permitted lift changes.

`verify_pa_green_primitive.py` passes fourteen exact checks, including all
constant-residue Green divergences, actual-source implication, weight and
orientation, full curve product rule, and all three literal compact
derivatives. The independent source-connection agent agrees with the
divergence signs, potential weights and descended coefficient formulas.
No certificate, Lean verification, solve PR, protected CI or acceptance
follows from this residue current alone.
