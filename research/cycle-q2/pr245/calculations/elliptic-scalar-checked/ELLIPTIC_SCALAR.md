# Three-input scalar equation on the descended paired-cubic chart

This is an additional explicit representation of the remaining proper primitive problem. The actual sparse product is the one in EXACT_EULER_REDUCTION.md. Let p=1/τ, u=I/b² and work with passive coordinates y,T,u. The plane cubic with active coordinates x=b,p,z has equation

```text
G=a x^3+b_0p^3+c z^3+d x^2p+e p^2z+f z^2x,
```

where a=1/T+u⁶T³, b₀=1+y⁶, c=T+1/T, d=uy/2, e=y/2, f=u/2. In affine z=1 this is the equation J_D−J_C=0. In the paired-ratio variables of Discussion 61 it is precisely α⁻³ times the paired cubic evaluated at (1,b,αp), with T=α³, u=β/α², y=γ. Thus the elliptic fibration itself is the previously known one, here on its legal degree-three descent. The original fourfold dominates this torus by the monomial change p=1/(X₀Y₀), b=X₁²/X₀², T=Y₀³/X₀³, I=X₁³Y₁/(X₀²Y₀²), y=Y₂, of degree 12.

## Physical density and central second variation

Use base volume dy∧dT∧du and the standard projective Ω=x dp∧dz−p dx∧dz+z dx∧dp. With these orders the physical source is (1/6)Res of NΩ/G³ times the base volume, where

```text
 N=(u²/6)xpz⁴+(2u/T)x³pz².
```

Indeed before u substitution its ambient form up to the factor 1/6 was (pI²/(6b⁵)+2pI/(bT))dI∧dp∧dT∧dy∧db/G³. The first factor acquired b² from the dependent-volume change dI=b²du+2ub db, and the permutation to dy∧dT∧du∧db∧dp is even. The factor 1/6 comes from taking the second G-normal residue and the previous −1/12 in the mixed tensor.

On z=1 the volume divergence of Q=(up/3)(2x∂x−u∂u) is zero and

```text
 N=Q(G)-(u² y/2)(xp)² .
```

This writes the contribution of Q as an explicit exact total differential, since div(Q/G²)=−2Q(G)/G³. It is essential that Q differentiates the parameter u. Write ω=Res(Ω/G), replace G by G+εxpz, and let subscripts ε denote its central parameter derivatives at 0. Then the physical source after subtracting this explicit current is exactly

```text
 −(u²y/24) (∇_ε²ω) ∧dy∧dT∧du.
```


## Rational scalar forcing

Write A=I₄ and B=I₆ in the Weierstrass convention Y²=X³+AX+B. The paired cubic invariant formulas and their central jets were previously checked in Discussion 61, comment 19113007:

```text
  A=a e² f+b₀d f²+c d² e,   
  B=-(27a²b₀²c²+4a²ce³+4ab₀²f³+6ab₀cdef+4b₀c²d³-d²e²f²)/4,
```

and Aε=(9ab₀c−def)/2, Bε=ab₀ef²+acd e²+b₀c d²f, Aεε=0, Bεε=−A/6. The cubic and its Jacobian have identified rank-two proper differential modules via the canonical cubic-to-Jacobian degree-nine map (which multiplies invariant differentials by a fixed factor 3).

Let r=B²/A³. The three commuting rational derivations in the coordinates (y,T,r) on the algebraic extension Q(y,T,u) are

```text
 W_y=∂_y-r_y∂_u/r_u,    W_T=∂_T-r_T∂_u/r_u,    W_r=∂_u/r_u.
```

The physical volume in these coordinates is dy∧dT∧dr/r_u. Put a_i=W_i(A)/(4A), D_i=W_i−a_i and aε=Aε/(4A). After adjoining a fourth root of A the normalized elliptic curve is Y²=X³+X+λ, with λ=B/A^(3/2), λ²=r. Its invariant differential h satisfies

```text
  (4+27λ²)h_{λλ}+54λ h_λ+15h/4=0.
```

The script elliptic_scalar.py checks the literal relative exact differential that proves this. The physical ω is a constant multiple of A^(−1/4)h. Thus h_{rr}+b h_r+c h=0 with

```text
 b=(8+162r)/(4r(4+27r)),    c=(15/4)/(4r(4+27r)).
```

All resulting operators are rational before any root extension. Use e₀=ω and e₁=(∇_r+a_r)ω. The non-isotrivial elliptic family gives a proper cyclic frame generically; equivalently the elliptic Gauss–Manin Kodaira–Spencer entry at the λ direction is nonzero away from the discriminant and r=0. The elliptic discriminant and r_u are verified nonzero at (y,T,u)=(1,1,1).

With all ε derivatives computed holding (y,T,u) fixed, put

```text
 L=r_{εε}-2a_εr_ε-b r_ε²,    M=5a_ε²-c r_ε²,    m=-u²y/(24r_u).
```

Since Aεε=0, differentiating A^(−1/4)h(r) twice gives ∇ε²ω=M e₀+L e₁. In the mixed top class mL e₁ can be integrated by parts in r. Its scalar representative is

```text
            H=m M-W_r(m L)+a_r m L.
```

The full proper-base-current condition is the following three-scalar rational equation on the original rational physical field:

```text
            H=D_y U+D_T V-[D_r(D_r-b)+c]W.
```

To check completeness write six rational input coefficients in the two-dimensional basis. The three lower components along e₁ force the e₀ coefficient of the r-current to equal −D_y u₁−D_T v₁−(D_r−b)w₁. Substitution into its e₀ component gives the formula above by [D_i,D_j]=0. Conversely the three scalar inputs give a solution by taking u₁=v₁=0, w₁=W and w₀=−(D_r−b)W. All volume and scale derivatives are included. This concerns the proper elliptic module; further genus-one residue extensions may enlarge the allowed primitives in the total rational function field.

At (1,1,1), A=3/4, B=−111743/256, r_u=37202485247/27648, L=−6898901077/18720, M=−8/117, and H=3694096125952/52329946740623506175. elliptic_source_jets.py computes these with exact rational Taylor arithmetic. elliptic_scalar.py additionally computes independent Griffiths coordinates from two Macaulay solves (degrees 6 and 3) and their physical u derivatives. The closed formula must be compared against the central source: the sparse source differs by the displayed Q-current.

## One-parameter elliptic surface and marked points

For generic fixed y,T, A and B have degrees 7 and 12 in u. The minimal Weierstrass elliptic surface over P¹_u has a section at infinity (on the Jacobian), fundamental line bundle O(2), and 24 simple nodal fibres. Infinity is smooth because B has nonzero degree-12 coefficient. Squarefreeness of 4A³+27B² in characteristic zero follows from the y=2,T=3 specialization modulo 101: elliptic_good_fibre.py finds degree 24 and gcd with its derivative equal to one. This gives an elliptic K3 surface. The original genus-one cubic has three marked points at x=0 from (1+y⁶)p³+(y/2)p²+T+1/T=0. A degree at most three extension of Q(y,T) gives a section over all u.

The remaining inhomogeneous scalar equation has not been solved. The nonzero value of H alone does not obstruct a rational solution.
