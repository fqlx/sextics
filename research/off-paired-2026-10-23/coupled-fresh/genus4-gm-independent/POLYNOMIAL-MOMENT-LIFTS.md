# Actual polynomial-moment lift changes

The source remains the bound actual `Ssrc=(D-6)(D-5)h`, SHA256
`d725307869fcf3a2f064a0a6616eee78ea59f74dd3305fcb1d2408d3018f25b5`.
Every compact and infinity curve component is retained. These are exact
source-carrying scalar lift changes, not the final sextic primitive.

With the actual commuting `A,B,Z`, `D=6Z-2iA-2JB`, `Av=Bv=0`, and
`Zv=v`, the following identities hold for unrestricted rational `Q`:

```
PE(vZQ)=(Z-1)[v LEQ], LE=D(D+1)+A(Z+D/2+2),
PD(vZQ)=(Z-1)[v LDQ], LD=4JB^2+2B+A(Z+JB+1),
P3(vZQ)=(Z-1)[v L3Q], L3=A^3+v(Z+JB+2)Z(Z+D/2+5).
```

Also `alpha(vZQ)=d_w Q`. Therefore adding these exact moments to the
actual potentials changes `K/v` by `-LEQ,-LDQ,-L3Q`, respectively.
`audit_exact_moment_lifts.py` verifies all three unrestricted differential
identities, not only their leading parts.

## Explicit source-bound preimages

The authoritative low-to-high polynomial arrays are in
`actual-polynomial-moment-preimages.json`, SHA256
`9e708325c6e0ab88fb6c1c7859d6dcae25ceddc7a0fa844ec0859c192a42d33a`.
They specify

```
QF=i^-1*qF(u,w), QG=qG(u,w),
QH=i^-4*qHminus(u,w)+i^2*qHplus(u,w), u=J/i^2.
```

The four polynomial degrees are `2,2,24,12`, respectively. They are
literal polynomial antiderivatives of the polynomial parts of the actual
`alpha(F),alpha(G),alpha(Hpot)`. The four full derivative identities are
checked exactly in `QQ(u)[w]`.

Define

```
Fproper=F-vZQF, Gproper=G-vZQG, Hproper=Hpot-vZQH,
Jproper=K/v+LEQF+LDQG+L3QH.
```

The exact source equation becomes

```
Ssrc-PE(Fproper)-PD(Gproper)-P3(Hproper)=(Z-1)[v Jproper].
```

All three properized moments have explicit numerators of degree at most
two over `N0=9w^2-16u(1+w^3)`; those numerators are saved in the same
JSON. No residue is changed. Cubic properization can introduce a simple
fold pole in `Hproper` and an order-five fold pole in `Jproper`; its
order-five principal part must remain. Properization is not claimed to
preserve the earlier order-three fold bound.

## Literal CRT freedom

Write `T=1+w^3` and `L0=256T^5N0+729i^6u w^6=L/i^2`. Let

```
Ccrit=N0*T*L0+w*N0_w*T*L0+2w*N0*T_w*L0-w*N0*T*L0_w.
```

Then `Ccrit=w*N0*T*L0*(d_w log v)`. Changing the actual residue lift by
`Crt -> Crt+N0*g(w)` gives

```
delta_t=i^-4*w*T*L0*N0*g=ZQ,
delta_Hpot=vZQ, delta(K/v)=-L3Q.
```

This has an explicit polynomial `Q`, without an unevaluated integral.
If `Ccrit=sum(c_k w^k)` and `g=sum(g_m w^m)`, set

```
Q=i^-4*sum_{k,m} c_k*g_m*w^(k+m+1)/(k+m+1).
```

The full coefficient array `c_k` and the literal CRT identity are saved
and checked in the same source-bound data file.

## Actual decaying infinity representative

The parent construction supplies the preferred quadratic lift

```
QDinf=-27i^3 w^2/(10J)-5103i^5 w/(3040J^2)-729i^4 w/(440J).
```

It serves the actual two positive infinity coefficients of `Jproper`.
The remaining constant is now explicit in
`properized-infinity-gauge.json`, SHA256
`ed36d4b2ea0e098d9884cd8c1e878cc5725a6a13141780d01d4ab7a6a3d14518`.
That file binds the actual properization arrays and the parent's
`source-infinity-preimage-results.json`. It gives rational `c1(u),c2(u)`
such that

```
Jnorm=Jproper-LD(QDinf)-i^-1*c1(u)-i^-2*c2(u)=O(w^-1).
```

Their denominators are only `32768u^4(5u+16)^5`; the apparent cubic
discriminant cancels from both constants. The corresponding actual
potentials are `Fproper`, `Gproper+vZQDinf`, `Hproper`, and the scalar
identity has right side `(Z-1)[v Jnorm]`. Its fold bound remains five.

The infinity constant is computed from exact limiting Cartan rows, not
from fitting the full function. `construct_properized_infinity_gauge.py`
verifies the four unrestricted parameter-row identities and binds the
zero polynomial constant of the complete N-only primitive. Finite fold
corrections and their coupled curve-valued remainder are still required.
