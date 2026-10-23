# Six-conductor collision along Gamma

This is an exact local normalization calculation for the physical degree32 effective-graph support of cyclic-triple-residual. It does not construct a certificate or identify its global H20/source image.

Set

```
Gamma={Y0=Y1=Y2=0} intersect X,
X0=1, v=X1, w=X2,
Gamma: w6+(5/7)w3+1+v6=0.
```

At the generic point of Gamma, the ambient X is smooth and w can be eliminated etale. The pinned D32 is independent of w. It has exactly two normal homogeneous pieces in the three Y variables:

```
D32=f13(v;Y0,Y1,Y2)+f15(v;Y0,Y1,Y2).
```

After blowing up `(Y0,Y1,Y2)`, put `Y=e*(a,b,t)`. Its strict transform is

```
f=f13(v;a,b,t)+e²*f15(v;a,b,t).
```

The two homogeneous polynomials have 69 and 94 monomials in `(a,b,t)`. Their full coefficients are in `initial.pickle`; extraction from the literal D32 is coefficientwise exact.

## Normalization generator

Let `S=a6+t6`. There are exact polynomial decompositions

```
f=q*S²+b*r*S+b²*s,
q=q13+e²*q15,
r=r13+e²*r15,
s=s13+e²*s15.
```

The coefficients are in `strict_normalization.pickle/json`. In particular, write `K=(1+v6)*(196v6+171)`. Then

```
q13=-194481*K*(14av7+9av+14tv6+14t),
q15=-1944810*a*t²*K,
r13=-926100*a²*t4*K,
r15 is divisible by S.
```

The rational function

```
theta=q*S/b
```

is integral and homogeneous of degree six (using degree -1 for e). Its exact relations are

```
b*theta=q*S,
S*theta=-r*S-b*s,
theta²+r*theta+q*s=0.
```

On the six sections `b=S=0`, the two theta values differ by r. Modulo their ideal, `r=-926100*a²*t4*K`, independently of e. Hence the generator separates the ordinary double branches whenever K is nonzero.

For the initial cone e=0, it gives the complete normalization, not merely a finite intermediate algebra. Here is a verification of completeness. The generic plane degree13 curve has precisely six collinear ordinary nodes. A good fiber at v=1 over F1000003 has projective Jacobian ideal `(b,a6+t6)`, irreducible degree13 equation, and a smooth rational point; consequently it is geometrically integral. Its affine Jacobian length is six, its infinity chart has no singular points, and the remaining projective point `[0:1:0]` is smooth. Properness and the six explicit ordinary-node sections imply the same statement over Q(v). Independently, Singular normalization reports genus60, consistent with arithmetic genus66 minus six nodes.

Let A be the homogeneous coordinate ring of this initial cone and B its normalization. The finite algebra A[theta] is birational. Its quotient by A is generated in degree six, with annihilator exactly `(b,S)`: these elements annihilate it by the displayed identities, and an additional annihilator would have to vanish at both separated branches at all six nodes. Thus

```
A[theta]/A = (A/(b,S))(-6),
Hilbert series = z6*(1-z6)/(1-z)^2.
```

This already has every missing normalization section. Indeed, by duality and adjunction, the extra degree n sections of the normalization are
`6-rank(ev_nodes on degree 10-n forms)`. Since the six nodes are collinear this equals zero for n<=5, then 1,2,3,4,5 for n=6,...,10, and six for n>=11. The same dimensions follow from the displayed Hilbert series. Hence A[theta]=B, and the conductor in A is exactly `(b,S)`.

The same generator separates and normalizes the six ordinary double branches of the full strict transform near the generic exceptional curve. Its central normalized curve is smooth, so no additional generic-curve normalization is required there. This conclusion is local over the generic function field of Gamma. It is not a global conductor-sheaf formula on the original D32.

## Remaining collisions and scope

The exceptional curve of the blowup, after normalization, is generically a smooth genus60 curve over Gamma. Its own H20 does not automatically give a serving Gysin class, since it maps into a curve in X.

The separation coefficient K vanishes at the special Gamma points over `v6=-1` and `v6=-171/196`. Infinity also remains separate. These are tied to the ramification of the plane-sextic projection: for `u=w3`, `u²+(5/7)u+1+v6=0`, so u=0 occurs at the first locus and the quadratic discriminant vanishes at the second. The first locus also has three unramified sheets with u=-5/7; it is not entirely a ramification locus. No conclusion about those special local models, global coherent twists, or the actual source image is inferred from the generic computation.

Reproduction: run `normalize_initial.py`, then Singular on `node_check_mod.sing`; run `strict_normalization.py` for the full exact identities. The direct characteristic-zero genus pilot hit its45s cap; the fast finite-prime genus value is separately recorded, and the generic claim instead uses the explicit nodes plus properness argument above.

## Homogeneous intermediate algebra and generic graded defects

`global_normalization.py` extracts the original homogeneous identity directly:

```
D32=q20*S6²+Y1*r25*S6+Y1²*s30,
Theta=q20*S6/Y1, degree25.
```

The three coefficients have 11,21,492 terms. Its finite integral algebra has quotient `O_{Y1=S6=0}(-25)` wherever the generic node-separation argument applies. Further finite normalization on curves and the resolution's R1 defects are separate issues. Fresh owns the global finite-algebra/coherent calculation.

The exact generic-Gamma jet interpolation packet is `jet_interpolation.py/json/pickle`. Since `N_Gamma/X=O_Gamma(1)^3`, the initial exceptional family is a nodal plane degree13 curve with coefficient line `O_Gamma(19)`. Its exceptional conormal is `O_Gamma(-1)` times the plane `O(1)`. On the ordinary-node open set, the graded R1 lattices are

```
O_Gamma(-19-n) tensor H0(I_sixnodes(10-n))^dual, n=0,...,9.
```

Their ranks are `60,49,39,30,22,15,10,6,3,1`, totaling235. The dual H1 lattices are

```
H0(O_Gamma(22+n)) tensor H0(I_sixnodes(10-n)).
```

Each basis vector has the literal degree32 polynomial lift `Xmonomial*Yadjoint`. The X basis has X2 exponent below six, using the monic plane-sextic equation of Gamma. The Y adjoint basis consists of all monomials divisible by Y1 plus `(Y0^6+Y2^6)` times the remaining binary forms. This proves split surjectivity of all these graded restriction maps, equivariantly for mu3 and global-Y sign. Total target rank is31,995. Compatibility with the actual global Leray boundary and corrections to these lattices at special points is not asserted by this graded computation.

## Special T=196v6+171=0 locus

Put `z=w^3+5/14`. On Gamma, `T=-196*z²` exactly. At a conductor section `a6=-1`, write `E=e²`, `h=a*v`, `k=9h-5`, and after the conductor blowup set `S=b*eta`. Elimination of v by the literal F gives

```
T_b=-10*E*k-140*a*E².
```

The quadratic part of the resulting chart is `A*b*eta+U*b²`, where

```
A=(84375/4)*a*(28aE+k)²,
U=-(3125/2)*a²*(28aE+k)*(120aE*h+120aE+27h²+30h-25).
```

Both vanish at the extra finite points `E=-k/(28a)`. These points must not be classified from the e=0 slice alone. `T0_cubic_pilot.py` and `T0_weighted_pilot.py` retain the actual implicit F, a6+1=b*eta, all effective-graph coefficients, and compute local truncated jets at one good finite-prime point. The ordinary cubic has a singular line. The next natural initial form has weighted degree5 for `(e-e0,z,b,eta)` of weights `(1,2,2,1)`; its weighted projective surface is irreducible and normal in the recorded pilot. Because5<1+2+2+1, a normal surface of this type has H20=0. Characteristic-zero coefficients, all-orbit coverage, and the resulting complete local resolution remain to be certified; the finite-prime pilot alone does not settle them.

The special weighted model has now been promoted to an exact all-branch calculation. `T0_weighted_symbolic.py` uses `D=e²-E0` as the etale weight-one coordinate; no square-root choice is needed. It proves all lower-weight terms vanish in `QQ[a,v]/(a6+1,196v6+171)`. Under

```
D=-a³*u, z=a²*Z, b=a³*B, h=a*v,
```

the initial polynomial, up to a nonzero scalar, has coefficients in `QQ(h)`, `196h6-171=0`. This degree-six polynomial is irreducible by Eisenstein at19. `T0_normality.sing` computes the exact Jacobian dimension1 in affine4 over that field; the weighted projective surface is normal. `T0_weighted_exact.json/pickle` contain the scaled equation and exact scaling check.

`T0_surface_singularities.py/json` gives a complete direct inventory: **three A1 points and one A3 point**. In the eta=1 chart, eliminating Z by its critical equation leaves `B*(J(u)+B*K(u))`. The two distinct roots of J with B=0 give two nodes. Its shared root with K yields the additional node `B=189/80`. The u-axis chart has a rank-two Hessian and a nonzero residual fourth-power coefficient, giving A3. The remaining weight-two line is smooth on the coarse surface. All unit checks are exact in the coefficient field.

These DuVal sections suggest the full threefold weighted blowup has only cDV or finite quotient singularities there. Its exceptional discrepancy is `1+2+2+1-1-5=0`. The step from this explicit exceptional surface to rationality of the full local threefold is a separate geometric inference awaiting independent audit; no global source-serving conclusion is claimed from it.
