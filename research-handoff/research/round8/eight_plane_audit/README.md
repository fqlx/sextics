# Independent audit of the eight-plane source reduction

This audits the source packet in `../eight_plane_quartic`. It does not produce
a rational primitive or a certificate. Run `python audit.py`; the exact checks
are recorded in `audit.json`.

## Physical density

With original order `(X0,X1,X2,Y0,Y1,Y2)`, set
`U=z(1,u,v)`, `V=(1,r,t)`, `X=(U+V)/2`, `Y=(U-V)/(2i)`.
The determinant with columns `(X,Y), partial_z(X,Y), ..., partial_t(X,Y)`
is `i*z^2/8`. This computes the projective Euler contraction directly and
independently of the six-coordinate affine Jacobian. The actual source is
`A=i*(z^2-1)^3/64`; hence, with `F=zG`,

```
A Omega/F^2 = -(z^2-1)^3 dz du dv dr dt/(512 G^2).
```

There is no missing sign or factor in this formula. The physical normal
deformation still has degree six in `z`; it is `zG+epsilon*i*(z^2-1)^3/64`.
It must not be replaced by an unspecified deformation within quartics.

## Hermite reduction and finite correspondence

The saved universal coefficients satisfy
`N=P'G-PG'+BG`, with `N=(z^2-1)^3`, `deg P<=3`, `deg B<=2`.
The linear system's determinant is exactly `g4*Disc(G)`. The displayed P
coefficients have denominator `g4*Disc(G)` and the B coefficients have
denominator `Disc(G)`. The local double-pole residue is
`(N'G'-NG'')/(G')^3=B/G' mod G`.

The ordinary trace is zero: for `j<3`, Lagrange interpolation of `z^j` at
the four roots gives `sum alpha^j/G'(alpha)=0` by comparing the cubic
coefficient. This applies to `B/G'` because `deg B<=2`.

For depressed roots `t_i` and a tracezero cubic polynomial `rho(t)`, write
`w=t_i+t_j`, `y=w^2`. The saved formulas pass an exact labeled-root check:

```
R(y)=y^3+2p*y^2+(p^2-4r)*y-q^2=0,
rho(t_i)+rho(t_j)=w*f(y),
rho(t_i)=1/2 sum_{j!=i} (t_i+t_j)*f((t_i+t_j)^2).
```

Thus the common flag gives an invertible correspondence on the full
tracezero rank-three sector. Its map to the quartic cover has degree three;
its map to the oriented-pair degree-six cover has degree two. The factor
`1/2` in the inverse is correct. Complementary pairs replace `w` by `-w`.
The twist cannot be dropped by taking the ordinary trace to the cubic
resolvent.

The charged connection matrices use columns for derivatives of
`(w,w*y,w*y^2)`. Independently substituting `y_i=-R_i/R_y` gives the saved
matrices, and all three curvature matrices vanish identically.

## Exact remaining obligation

On the actual four-dimensional shape base, with the exact physical quartic
coefficients substituted, a rational current must still solve

```
sum_i (partial_i + y_i/(2*y))*u_i = -f(y)/512.
```

An exact solution would transfer back through finite trace and the explicit
Hermite correction. Neither the rational P1 fiber nor this finite
correspondence supplies that solution by itself. All calculations here are
identity checks and make no coniveau or unrestricted existence claim.

## A compact normal-coordinate lift

`normal_lift.py/json` gives a new exact circuit, with the inverse matrix left
unexpanded. Set `c0=-1/g0`, `c2=1/(5*g4)`, `w=c0+c2*z^2`, and let

```
M[k,i]=partial_i(g_k)-g_k*partial_i(g4)/g4,  0<=k,i<4,
r=rem_z((N-w*(G+z*G'))/z,G),
v=M^{-1}r,
Q=(-4*c2*g3-sum_i v_i*partial_i(g4))/g4.
```

Here `r` is its four coefficient column. The choices of `c0,c2` cancel the
constant and degree-six terms of the numerator. Consequently its quotient
by `z` is a polynomial of degree at most four. The definition of `M` gives
the exact identity

```
N=w*(G+z*G')+z*sum_i v_i*partial_i(G)+Q*z*G.
```

The matrix is generically invertible for the actual instance: at
`(u1,u2,v1,v2)=(1,2,3,5)` modulo `1000003` its determinant is `954506`.
All denominators are units there, so this proves nonvanishing over Q.

With `D_i=partial_i-(G_i/G')partial_z` on the quartic field and
`C0=div(v)+Q`, differentiating the normal identity gives

```
rho = (-2/g0+C0*z+4*z^2/(5*g4))/G'
      -sum_i D_i(v_i*z/G').
```

For example, clear `(G')^3` and use
`N'G'-NG''` for the original residue numerator; the identity follows by
one `z` derivative of the preceding polynomial identity. This trades the
quartic discriminant for `g0`, `g4`, and the Jacobian matrix determinant.
It is an explicit partial current, with a remaining nonzero three-component
source. It is not a certificate. The actual source factor remains `-1/512`.

## Completed bounded searches

`current_search.py` tests the exact cleared source equation with
`u_i=P_i/G'`, `deg_z P_i<deg G`, and total polynomial base degree at most
the specified bound. It supports both the quartic and the smaller global-Y
cubic source. The cubic is selected by `EIGHT_MODEL=cubic`; its actual
source factor is `+1/2`, and its normalized numerator is `N=t^2`.

Both screens through total base degree six are inconsistent modulo
`1000003`. The cubic weighted union `cubic_weighted_poles.py` also includes
the boundary poles `g0(a,b)` and `g3(c,d)`; its 1596 columns have rank 1572,
with augmented rank 1573. These are stated only as bounded finite-prime
screens. Failed under-sampled pilot fits are explicitly archived with
`INVALID_undersampled` names; no positive candidate survived an independent
fiber check. The final sampler uses the tracezero rank rather than the
nominal algebra dimension when choosing its sample count.

## A complete selected moving-Segre source-image test

`cubic_source_image.py` takes

```
D=det[U,V,M1*V],  M1=[[1,2,3],[0,2,1],[1,0,3]].
```

It includes every degree-six source and degree-four numerator field in E1,
then imposes E2 with its constant quotient. The E1 system has rank 1182 and
nullity 36; E2 leaves exactly 35 source directions. These are precisely the
globally exact sources `V(F)` for tracezero linear fields `V`. Their
independence and existence in characteristic zero, together with the
modular rank, prove this statement over C. The global-Y translate adds no
source direction, and adjoining the actual `A` increases the union rank
35 to 36. The result concerns only this selected cubic and its translate.

## Complete coordinate-polar support tests

`euler_support.py` handles `D=V(F)` for a three-coordinate Euler field `V`
containing exactly one of `X0,Y0`. Because `V(A)=3A` and `div(V)=3`, the
complete E1 seed is `N=A*V`; its E2 source is `A*(6D-V(D))`.
All 315 quadratic Jacobian Koszul corrections and all 462 degree-six
quotient coefficients are retained in the degree-twelve E2 system.

There are always 35 independent kernel pairs: for a linear field `L`
modulo the full Euler field `E`, put

```
T=F*L-L(F)*E/6,
Q_T=D*div(L)-L(D).
```

Then `T(F)=0` and `B_D(T)=F*Q_T`. Explicitly
`T_i=sum_j F_j*(x_j*L_i-L_j*x_i)/6`, so these lie in the included quadratic
Koszul space. They are independent because `T=0` forces `L` to be a
constant multiple of `E`. Thus the 777-column matrix has rank at most
742 over Q. Attaining rank 742 and augmented rank 743 modulo a good prime
therefore gives a characteristic-zero exclusion for the selected support,
not merely a numerical obstruction.

The six complementary coordinate splits containing `X0` and not `Y0` are
saved individually as `euler_support_X0_*.json`. This is a finite list of
supports and makes no claim about all degree-six denominators.
