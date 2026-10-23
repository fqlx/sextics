# Parameter-dependent elliptic contraction: the exact correction

This records a conditional constructive extension of the accepted contraction
identity. It does not supply the missing scalar primitive for the new Fano
complete intersection, or a certificate.

Let `delta` be the invariant elliptic derivation, `DX_i,DY_j` commuting
coefficient derivations, and `Res` the selected finite-residue functional.
Assume it commutes with the coefficient derivations and kills `delta`.
Suppose actual rational scalar/current data satisfy

```
delta f + sum_i DX_i Cf_i = alpha,
delta g + sum_j DY_j Cg_j = beta*h,
Res(f*h)=3alpha−sum_i DX_i xi_i.
```

No independence of `g` from `X`, `f` from `Y`, or `beta` from `X` is assumed.
Define exactly the same candidate output currents as in the accepted proof:

```
Ux_i=[Res(Cf_i*g)+beta*xi_i]/3,
Uy_j=Res(f*Cg_j)/3.
```

The full identity, with every coefficient derivative retained, is

```
3(divX Ux+divY Uy)
 =3alpha*beta + alpha*Res(g)
  +Res[sum_i Cf_i*DX_i(g)+sum_j Cg_j*DY_j(f)]
  +sum_i DX_i(beta)*xi_i.
```

To prove it, expand both product derivatives. Substitute the two scalar
equations and combine `−(delta f)g−f delta g=−delta(fg)`, whose residue is
zero. Substitute the theta pairing and differentiate `beta*xi_i`.
The original independence hypotheses remove precisely these extra terms.

There is an additional term when the second primitive is first constructed
as `g(E2;E1,X)` and the elliptic factors are then restricted to a diagonal.
If its scalar equation controls only `delta_2 g`, the actual diagonal
derivative is `delta_diag=delta_1,param+delta_2`. The full product identity
then has the extra contribution

```
+Res(f*delta_1,param g).
```

This is separate from `DX_i g`. It remains present even when all ordinary
X parameter derivatives vanish. Translated diagonals must use their full
moving-map first jets as well.

Generic pole separation may still prove `Res(g)=0` for a parameter-dependent
primitive, but does not set `Res(Cf_i DX_i g)` to zero. Regularity of `g`
and its derivatives at the selected poles is insufficient because `Cf_i`
may have poles there.

## A sufficient weaker independence condition

Suppose the first construction is Y-independent, and actual rational
mixed data `H_ij` satisfy

```
DX_i(g)=sum_j DY_j H_ij.
```

Then the troublesome cross term has the explicit primitive

```
Res(sum_i Cf_i DX_i g)
 =sum_j DY_j Res(sum_i Cf_i H_ij).
```

Subtracting this current, and treating any `DX beta` contribution, gives
the desired contraction. This asks for independence modulo Y-divergences,
which is weaker than literal `DX_i g=0`.

A finite connection version would require **primitive-jet identities**

```
DX_i g_a=sum_b A_iab g_b+sum_j DY_j H_iaj.
```

The first scalar construction would then have to solve the corresponding
dual covariant current equations. This can supply a finite constructive
closure if those specific data are produced. Merely differentiating the
second scalar equation and recognizing its source connection only proves

```
delta[DX_i g_a−sum_b A_iab g_b]+divY(...)=0.
```

The homogeneous term in square brackets need not be a Y-divergence. The
rank-two connection of the physical cubic source therefore does not, by
itself, supply the primitive-jet identity.

## The new Cardano/Fano incidence

The new source-carrying incidence is

```
G1=S³+T³−H(X),
G2=c³−C(Y),
Q=B(X,Y)+3cST,
p=−(S+T)/c.
```

On `ST!=0`, eliminating `c` yields the second defining polynomial

```
D_Y=C(Y)+B(X,Y)³/(27S³T³).
```

Extending it to the Fano companion means using
`J=D_Y−d³−e³`. The physical source remains the specified boundary/normal
residue, with its `d,e` poles; an arbitrary polynomial source on `J=0`
does not replace it.

For example, near the physical section `d=e=0`, set `d=t,e=lambda*t`.
Then the exact blow-up identity is

```
dd∧de/(d e)=dt/t∧d lambda/lambda.
```

The added boundary poles are therefore genuinely logarithmic, with the
physical curve residue as coefficient. Choosing both auxiliary coordinates
to vanish at the same polynomial-curve endpoint does not turn them into
an automatically integrable second-kind pole. The simultaneous cubic
scaling of `d,e` preserves this logarithmic source.

For any first-block parameter derivation `D`, the exact derivative is

```
D(D_Y)=D(C)+B²/(9S³T³)
                  *[D(B)−B(D(S)/S+D(T)/T)].
```

It retains the mixed X and first-elliptic dependence. Higher derivatives
also differentiate inverse normal and incidence Jacobians. The fact that
`B` is quadratic in Y does not imply that the rational primitive `g`, its
denominators, or its X derivatives have bounded polynomial degree.

Thus separate polynomial-curve constructions on the first weighted Fano
hypersurface and the second Fano complete intersection do not yet establish
the parameter-dependent contraction. A useful new input would be the
actual boundary source theorem together with the displayed primitive-jet
closure, or a jointly compatible polynomial-family/homotopy construction
which proves it. Neither is supplied here.
