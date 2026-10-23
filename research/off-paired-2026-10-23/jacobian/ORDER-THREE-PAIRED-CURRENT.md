# Order-three paired potential with the physical correction retained

This constructs the universal paired scalar potential and the resulting
actual physical current. Its nonzero density correction is retained; no
primitive for a nontrivial paired physical source has been established.

Normalize the physical cubic as

```
rho=(H/C)^(1/3), b=B/(H^(2/3)C^(1/3)), p=rho*r,
r³+b*r+1=0.
```

On the fixed elliptic Galois cover use

```
E: Y²=X³−16,
r=−4/X, b=(X³−64)/(4X²).
```

Let `k²=−16` and `T=(0,k)`. Translation by `T` is explicitly

```
T(X)=2k(k−Y)/X²,
T(Y)=k+64(Y−k)/X³.
```

It has order three and fixes `b`. The checker verifies the elliptic
equation, `b(TP)=b(P)`, and `T²(P)=P−T`. The involution
`sigma:(X,Y)->(X,−Y)` fixes `r` and gives the quadratic subgroup of the
full S3 cover.

The normalized **actual source** and its scalar potential are

```
R0=HC*R=−64X³(X³−64)/(X³+128)³,
psi0=8X/(X³+128),
d_E psi0=R0 db.
```

Thus on the fixed elliptic curve there are genuine exact paired identities

```
d_E[(1−T)psi0]=(R0−T R0) db,
d_E[(1+T)psi0]=(R0+T R0) db.
```

The first has an invertible source operator on the trace-zero component:
`(1−T)^(-1)=(2+T)/3`. The second has inverse `−T` there. These inverses
become relevant only after obtaining an exact **physical** paired current.

## Actual physical pullback

The physical potential is

```
psi=H^(−1/3)C^(−2/3) psi0=−p/(2g),
partial_B psi=R,
```

where the last derivative holds at fixed `H,C`. Choose the original
physical base `(x,a,u,v)` and put

```
Y=−H_a partial_x+H_x partial_a,
J=Y(B)=H_x B_a−H_a B_x,
V_B=Y/J.
```

Then `div Y=0`, `V_B(H)=V_B(C)=0`, `V_B(B)=1`, and
`div V_B=−Y(J)/J²`. Since the finite deck map fixes the physical base,
it commutes with the extended physical derivations. The exact physical
paired-current identity is therefore

```
div[(psi−T psi)V_B]
 = R−T R −(psi−T psi)Y(J)/J².
```

There is an identical formula with both minus signs in the pair replaced
by plus signs. This is an actual rational current identity on a finite
physical cover. The final term is a genuine remaining source. In the
fixed-Fermat-product chart the same calculation replaces `Y,J` by an
angle derivative `delta_i` and `delta_i(B)`; its correction is
`−(psi−Tpsi)delta_i²(B)/(delta_i(B))²`.

## Why deck inversion alone does not close the current

Both `psi` and `R` are sigma-even and have cyclic trace zero. Their
conjugates generate copies of the same standard S3 module, with the
same sigma-fixed orientation. Consequently a constant group-ring
operation which annihilates the potential correction also annihilates
the desired source component. In particular the noninvertible
`1+T+T²` average cannot be combined with the displayed inverse to erase
the correction.

A useful new input would be an actual incidence or companion current for
`R−TR` (or `R+TR`) whose **full** physical correction either has its own
rational primitive or lies in a different, removable character. The
universal paired scalar potential above supplies neither fact.
