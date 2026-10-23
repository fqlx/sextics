# An explicit compact i-current with its full density correction

This is a constructive current for the actual Euler-reduced source. The
remaining density correction is still nonzero and has not been served.
In particular, this is not a rational primitive along fixed j,w and not
a certificate of the original sextic.

Use the descended curve and compact frame

```
ay=x^3,
y^2+v(a^2+i x^2+j a x+x+1)=0,
Jbar=v(2a^2+jax)-2y^2,
nu_N=v N dx/Jbar,
omega=v x^2 dx/Jbar,
zeta_hat=y dx/x,
D=-2i partial_i-j partial_j+6v partial_v.
```

The compact frame is ordered

```
[1,x,x^3,x^4-v(i-j^2/4)(i-5j^2/4)x^2/8,
 a,ax+jx^2/2,y,yx].
```

The simple differential Psi_i=(x/a)dx=y dx/x^2 has the literal derivatives

```
partial_i Psi_i=nu_b,
partial_j Psi_i=omega.
```

It has a finite Pa residue and must not be treated as compact. Its complete
finite, infinity, compact and exact decomposition is

```
Psi_i=zeta_hat/2+j omega+nu dot Ci+d_x Gi,
Ci=[0,0,-j/6,0,0,6,2i-2/3,-i/3],
Gi=-y/x-y/3.
```

All terms occur literally in the curve function field. The D Cartan
correction is also explicit:

```
nabla_D zeta_hat=3 zeta_hat+nu_b-d_x y.
```

Consequently

```
Ui=(2-nabla_D)Psi_i+zeta_hat/2
```

is compact: the finite residue cancels and the infinity component cancels.
Its eight compact coefficients are

```
Ui_coeff=-e_b/2+(2-nabla_D)(Ci+j omega).
```

Here every derivative of Ci, j and the frame is included. The rational
eight-vector is exported in `i-source-compact-primitive-results.json`.
If fD denotes the complete stored rank-nine D fiber-primitive row, an
explicit fiber primitive for this reduction is

```
Fi_U=y/2+(2-D)Gi-fD dot (Ci+j omega).
```

No marked root or selected numerical matrix is used. The generic matrices
and all their rational fiber primitives are retained.

## Actual source current

Put Q=(4I-GammaD)e_b, the actual Euler compact vector. The exact relation is

```
nabla_i Ui=Q+e_bq/2.
```

Thus for the actual density t=hsrc/(6v^2), the native current P_i=t Ui
serves tQ except for the full correction

```
-partial_i|j,v(t) Ui-(t/2)e_bq.
```

The first term must not be omitted. On the physical inverse branch

```
T=1+w^3,
N=9i^2w^2-16j^2T,
M=256T^5N+729i^6j^2w^6,
v=64j^2wT^2N/(9i^2M),
a0=hsrc v_w/v^2=54i^3wT/(j^2N),
t=a0/(6v_w),
partial_i|j,v=partial_i|j,w-(v_i/v_w)partial_w.
```

For the physical volume di∧dj∧dw, the actual Piola current therefore has
both components

```
P_i=v_w t Ui=(a0/6)Ui,
P_w=-v_i t Ui,
P_j=0.
```

The remaining physical density is

```
-v_w[partial_i|j,v(t)]Ui-(a0/12)e_bq.
```

This source is a concrete full-base alternative to the j-current. Its
physical w component is essential; it is not an i-only solution at fixed
j,w. All corresponding rational fiber currents follow from Fi_U and the
stored eight connection primitives.

`build_i_source_compact_primitive.py` passes sixteen exact checks: all nine
generic cleared source-matrix identities, zero infinity coefficient, the
literal curve derivatives, the complete Psi_i decomposition and D Cartan
correction, and finite-residue cancellation. Input connection hashes are
bound in the result JSON.

The restricted fixed-j,w reconstruction checkpoint in
`i-direction-point-feedback.json` is internal feedback at j=w=1. It has
not been promoted to an independently verified generic exclusion. The
construction has returned to the full-base Ui/Uj currents with their
explicit density and branch corrections.

No certificate, Lean verification, protected CI or acceptance is claimed.
