# Coupled Klein character: source-preserving line channel, not a solution

Research stopped at the user's instruction, before any support/certificate claim. Exact target is `/workspace/sextics/data/klein-coupled-character/instance.rec`; no protected file was changed.

## Target and provenance

Write `(x,y,z)=(X0,X1,X2)`, `c=5/7`, and

```
K=x^5*y+y^5*z+z^5*x,
F=K+g(Y)+c*(x*y^3*Y0*Y1+2*x^3*z*Y1*Y2+3*y*z^3*Y0*Y2),
g=Y0^6+Y1^6+Y2^6,
A=x^3*Y0^3.
```
The order-seven action has X weights `(1,2,4)` and fixes Y. F and projective volume have character zero, A has character 3. The known cubic/Fano quotient serves character zero only. Averaging cannot serve this target. Read `why.md`, `provenance.json`, and `docs/04-known-locus-and-frontier.md` section 4.3. Existing scratch searches only excluded denominator degrees 1 through 4 (`alternate-audit/low_degree_e1_screen.json`); this is no unrestricted exclusion.

## Exact quotient and actual density

```
U=x^2*y/z, V=y^2*z/x, W=z^2*x/y,
p=U^2*W+U*V^2+V*W^2,
P=p+UV*Q0+UW*Q1+VW*Q2+g,
Q0=c*Y0*Y1,Q1=2*c*Y1*Y2,Q2=3*c*Y0*Y2.
```
The exponent determinant is 14. Over Y directions, its cubic-surface homogenization is

```
p(U,V,W)+T*(UV*Q0+UW*Q1+VW*Q2)+T^3*g=0.
```
The scalar factors from fixing a Y direction are those of the known construction. The full six-coordinate Jacobian of `(U,V,W,T=Y0^2,alpha=Y1/Y0,beta=Y2/Y0)` is `28*x*y*z/Y0`. Thus the actual target density after division by this Jacobian is

```
rho*T^2/28,  rho=x^2/(y*z),  rho^7=U^4*W/V^5.
```
In particular rho has physical order-seven character 3; it must be retained.

## Constant genus-three curve on a quotient line: character passes

Let a line on the cubic surface have rank-two projection to P2_(U,V,W), with Pluecker minors

```
a=pUW, b=pVW, d=pUV,
b*U-a*V+d*W=0.
```
On its generic locus set

```
t=b*U/(a*V),
U/V=(a/b)*t,
W/V=(a/d)*(1-t),
kappa=a^5/(b^4*d).
```
Then exactly `rho^7=kappa*t^4*(1-t)`.

After adjoining `e^7=kappa`, set `eta=rho/e`. The fixed curve is

```
C3: eta^7=t^4*(1-t).
```
It has genus 3. Its holomorphic differential

```
omega=eta*dt/(t*(1-t))=t^3*dt/eta^6
```
has orders 3,0,1 at t=0,1,infinity (up to an irrelevant sign in the second equality if the equation uses t-1). With physical sigma acting on eta by zeta^3, omega has precisely character 3. Thus the proposed channel is not killed by deck orientation. Holomorphic eta-deck characters are 1,2,4; multiplying by the physical weight 3 gives physical characters 3,6,5.

The holomorphic 2-form channel on the descended isotrivial curve family requires the inverse deck character in H10 of the **twisted** line-parameter cover. The untwisted line surface's irregularity is insufficient.

## Relative line surface: BWB correction and raw irregularity

Let B=P2_Y and E=O(2)^3+O. The relative line scheme lies in Gr_B(2,E) and is cut by the rank-four section `Sym^3(S*) tensor O(6)`. For a regular section, relative Koszul+Borel-Weil-Bott gives:

| Koszul k | nonzero relative cohomology | split bundle on B |
|---|---|---|
|0|R0|O|
|1|R2|O + O(-2)^3|
|2|R2|O(-2)^6 + O(-4)^3 + O(-6)|
|3|none|0|
|4|R4|O(-4)^6 + O(-6)^8 + O(-8)^6|

The k=1 term is essential. For `Sym^3 S = Schur(0,-3) S*`, BWB has `(3,-1,1,0)` after adding rho, all distinct, length two. Omitting it would give fiber Euler characteristic 31 rather than the correct 27. The full fiber Euler is `1-4+10+20=27`.

The only hypercohomology contribution to H1 is the O summand at k=1,R2. It has no possible nonzero incoming/outgoing differential. Therefore the **regular raw line scheme** has h1(O)=1 and chi(O)=243 (h2=243 if connected). Smoothness/normalization of the exact target's line scheme was not checked, so this is a conditional scheme-cohomology calculation, not a completed resolution theorem.

Geometrically a generic line meets T=0 at a point of the constant smooth cubic E0: `p(U,V,W)=0`, giving a map from the line surface to E0. E0 has j=0: diag(1,zeta3,zeta3^2) preserves p up to scalar and fixes its three coordinate vertices. This explains the surviving elliptic irregularity.

## Crucial twist obstruction/gap

Kappa is not generally a function of the intersection point p alone. Let B0 be the universal incidence `(p,ell)` with p on E0 and ell a line through p. B0 is a ruled surface over E0, and t(p) varies in its rational fiber. On B0,

```
kappa=R_E(p)/(t(p)^4*(1-t(p))), R_E=U^4*W/V^5.
```
Let `K10 -> E0` be the cyclic cover `rho_E^7=R_E`; this is birational to the original smooth plane Klein sextic K=0, genus 10. Then the normalized kappa cover of B0 is birational to

```
(K10 x C3)/diagonal mu7,
```
with `e=rho_E/eta`. Consequently its H1 only retains H1(E0): the nontrivial eigenspaces of H1(K10) and H1(C3) individually do not survive the diagonal quotient. This rules out treating the twist simply as the pullback of K10. The actual line surface has an additional generically finite map to B0 imposed by the Y coefficients. Its kappa cover may have further irregularity; this was not computed. Its nontrivial deck H10, the actual Gysin projection of A, and an inverse correspondence remain open.

## Untested continuation idea, not a result

At g(Y)=0, the quartic X-leading term along X=0 is
`x*y^3*Y0*Y1+2*x^3*z*Y1*Y2+3*y*z^3*Y0*Y2`,
a diagonally rescaled Klein quartic when all Yi are nonzero. This suggests a constant CM genus-three curve in a boundary exceptional model. Neither E1 membership of A*g nor any Gysin/source projection was tested. Do not present this as a certificate or as established support.
