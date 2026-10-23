# A source-retaining coupled current in the constant-density chart

This is an exact constructive reduction, not a primitive or certificate. It
retains both components of the cubic connection and all physical coefficient
derivatives.

Use coordinates `(Z,h,u,v)` and

```
H=1+Z^-2+h^6, C=Z^2+u^6+v^6,
B=u/2+hv/3+huv/(2Z), k=B^3/(CH^2), t=4k+27,
Omega=-(1/3)dZ dh du dv.
```

The scalar fields `V,W` satisfy

```
dV=-2W dlog(k),
dW=[3V+(27-2k)W] dlog(k)/t,
R=W/(CH).
```

All divergences below are ordinary coordinate divergence, since the actual
volume has constant density. Put

```
E=h partial_h-v partial_v,
K=2C h^6-H v^6,
L=2(Z^2+u^6)h^6+(1+Z^-2)v^6,
U=E/(12K).
```

The physically important identities are

```
div E=0, E(B)=0, E(K)=6L,
E(log k)=-6K/(CH),
U(log k)=-1/(2CH), div U=-L/(2K^2).
```

Consequently the actual first current `V U` has the complete divergence

```
div(V U)=R-L V/(2K^2).
```

Its remaining `V` component is not omitted or identified with a universal
trace. In particular this identity is not the excluded pure-`V` solution:
`div U` is generally nonzero.

Set

```
f=(27-2k)/(2t), c=3(27-23k)/t^2, P=f V+W.
```

There is an exact one-variable connection identity

```
dP=c V dlog k.
```

Thus any rational base vector field `D` satisfying

```
div D=0,
D(log k)=t^2 L/[6(27-23k)K^2]
```

would complete the actual current:

```
J=V U+P D,
div J=R.
```

Here `D` is independent of `U`. Both `V` and `W` enter `J`, and all of
`H,B,C` may vary along `D`; the sufficient criterion does not impose
`D(H)=0`, `D(B)=0`, or `D(C)=0`.

For the rational exact symplectic form
`omega0=dZ wedge dh+du wedge dv`, a narrower constructive option is a
rational Hamiltonian `S`. With

```
{S,G}=S_Z G_h-S_h G_Z+S_u G_v-S_v G_u,
D=( -S_h, S_Z, -S_v, S_u ),
```

one has `div D=0` and `D(G)={S,G}`. The one remaining equation is

```
{S,log k}=t^2 L/[6(27-23k)K^2].
```

No such `D` or `S` has been constructed. A generic rational Hamiltonian
equation does not have an automatic rational solution. In particular,
replacing its right-hand side by a coordinate antiderivative or dropping
the derivatives of `H,C,B` would invalidate the source identity.

The affine `h` coefficient of `B` also gives the older first current
`p_B/(2 B_h) partial_h`, whose defect is `H_h p_BH/(2B_h)`. It does not
cancel the displayed `L V/(2K^2)` defect by itself. The criterion above
uses a different explicit `U` and keeps the second independent current.

`coupled_euler_current.py` checks the physical vector identities, the
canonical operator identity, and both complete current coefficients.
