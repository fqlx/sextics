# Polynomial-potential source-current handoff

Research stopped at the user's request. No external writes were made.
The immutable off-paired sextic primitive remains unsolved. The results below
are exact partial source currents with their residuals retained.

## Verified full-base identities

Coordinates are `(i,j,v)`, flat volume `mu=di wedge dj wedge dv`,
`V=6v partial_v`, and `D=V-2i partial_i-j partial_j`.
The compact basis and ninth infinity form are the ones in
`../ruling-source/full-base-connection/FULL-BASE-COMPACT-PDE.md`.
Indices below are zero based; `eb=e6` and `ebq=e7`.

The polynomial vectors `W,Vi,U` are stored in the input files referenced by
`full-base-polynomial-potential-audit.json`. They satisfy

```
nabla_i W=-v*(e0+2i*e1+j*e4)/6,
nabla_j W=e7,
nabla_V W=6W-6e2-3j*e7,
nabla_i Vi=U+(j/2)e7,
nabla_j Vi=Ui+(j/2)e2,
nabla_V Vi=6Vi+6e1-(3j/2)eb,
Ui=[0,0,j/6,0,0,0,2/3,i/3].
```

`verify_full_base_polynomial_potentials.py` checks all six relations in
all nine rows by exact generic cleared polynomial identities: 54 row
checks. Three additional unrestricted-density product/divergence checks
pass, for a total of 57. The ninth row cancels identically and was not
omitted. Runtime:

```
/workspace/tooling/sextics-venv/bin/python \
  coupled-fresh/genus4-gm-independent/verify_full_base_polynomial_potentials.py
```

Saved audit SHA256:
`725039e7ecc78be0b338c4cceef22a7ca268ad0bcfd6fcfe656518750c976abc`.
It binds all four input arrays by SHA256.

## Completed direct actual-source current

Algebraic elimination of `Ui,e2` in the verified relations gives

```
eb=(3/2)nabla_j Vi+(j/6)nabla_V W
   +((j^2-i)/2)nabla_j W-jW.
```

For the actual source put

```
g=(D-5)hsrc/(6v^2).
```

This is the original compact source `g*eb` in the displayed flat volume.
Define the coefficient currents

```
P_i=0,
P_j=(3/2)g*Vi+((j^2-i)/2)g*W,
P_v=jv*g*W.
```

Their exact covariant divergence is

```
g*eb+(3/2)g_j*Vi
 +[jv*g_v+((j^2-i)/2)g_j+3j*g]*W.
```

Thus the source residual still to serve is

```
Rdirect=-(3/2)g_j*Vi
        -[jv*g_v+((j^2-i)/2)g_j+3j*g]*W.
```

This direct formula is derived by substitution and the product rule from
the 57-check packet; no separate final source-current executable was run
after the stop instruction. All `g_j,g_v` derivatives hold the other native
coordinates fixed and include every derivative of the actual implicit
physical branch `w(i,j,v)`. They cannot be replaced by derivatives at
fixed `w`.

The actual finite physical cover is

```
T=1+w^3,
N=9i^2*w^2-16j^2*T,
M=256*T^5*N+729i^6*j^2*w^6,
v=64j^2*w*T^2*N/(9i^2*M),
hsrc*v_w/v^2=54i^3*w*T/(j^2*N).
```

There is no division by `j` or `v` in the polynomial coefficient factors
of this direct current; the actual `g` and its derivatives retain their
own full denominators. This does not assert an improvement in all poles
or eliminate any compact component.

## Alternative mixed current already saved

For `t=hsrc/(6v^2)`, the source remainder `t*nabla_j U` has current

```
P_i=-t_j*Vi,
P_j=t*U+(j/2)t_j*W,
P_v=0,
```

and exact residual

```
Rmixed=t_ij*Vi-(t_j+j*t_jj)*W/2.
```

This is recorded in the machine-readable audit. It is an alternative
partial reduction; its residual is not known to vanish.

## Literal reconstruction and limitations

For either displayed vector current use the full stored connection fiber
primitives `f_i,f_j,f_v=fV/(6v)`:

```
Jbase=-sum_p (nu dot P_p) wedge contraction_partial_p(mu),
Jfiber=-sum_p (f_p dot P_p)*mu.
```

The second line is essential. It cancels the literal fiber-exact pieces
created by the connection, rather than asserting only an identity of
cohomology classes. Every infinity companion remains in the checked
rank-nine connection.

Outstanding: serve the displayed nonzero actual residual, reconstruct
and descend a full rational primitive, check denominator admissibility,
verify the immutable cleared identity, and complete the formal
certificate. No rational primitive or final certificate is claimed.
