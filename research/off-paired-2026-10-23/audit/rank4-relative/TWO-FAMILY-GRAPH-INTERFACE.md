# Target-bound interface for the genus-two isomorphism graph

Write w=X0, x=X1, y=Y0, z=Y1, u=X2, v=Y2. The actual homogeneous
background and endpoint polynomials are

```
H=w^6+x^6+y^6+z^6+w^3xyz/2,
D=H-w^6-z^6, C=x^3z/2+w^2xy/3, Cb=-w^3z/2,
F=H+u^6+v^6+Cuv.
```

The endpoint and background genus-two families become isomorphic along

```
Dg=8D^2 C^3+w^9 z^3 H^2=0.
```

Dg is homogeneous of degree24 and nonzero (value4 at w=z=1,x=y=0).
It is complex-coprime to F: every factor of Dg is independent of u,v,
whereas F is monic of degree6 in u. Thus a nonconstant common factor
would have to divide its leading coefficient1. No irreducibility theorem
or finite-field nonmembership argument is required for this side condition.

On the generic graph, let

```
r=H Cb/(D C)=-H w^3z/(2DC).
```

Then r^3=H/D and r^2=C/Cb. There is no need to adjoin a cube or square
root on this generic open. The maps are

```
p=r q, Zp=r^3 wb,
wb^2=(D+Cb q)^2-4q^6.
```

This is a map between two curve points. On the parameter support Dg=0 the
actual endpoint point p and actual background point q remain independent.
For a two-point kernel write P=p/r and retain both P and q; the equality
P=q describes the diagonal, not the whole parameter support. A function
such as P^3/Y(P) cannot be replaced by q^3/wb away from that diagonal.

The relative basis and discriminant identities are

```
omega_j(endpoint)=r^(j-2) Omega_j(background),
Delta(endpoint)=r^12 Delta(background).
```

When r varies, the literal pullback contains the additional term
`r^(j-3) q^(j+1) dr/wb`. It cannot be omitted in a global current.
Coordinate boundaries and discriminant intersections also require the
actual source corrections. A relative curve isomorphism and a legal
candidate support do not establish a closed residue, source Gysin match,
or certificate. These remain the constructive obligations.

`verify_two_family_graph.py` checks eight exact symbolic groups.
