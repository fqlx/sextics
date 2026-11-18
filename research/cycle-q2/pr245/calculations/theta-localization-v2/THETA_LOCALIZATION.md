# The residue connecting map for Θ

Work over K=ℚ(I,J). Write E_C and E_D for the proper first de Rham modules of the genus-four and genus-ten curves, and E⁺=E_D+KΘ for the submodule of the punctured genus-ten curve obtained by adjoining Θ=(1/3)b⁻³dlog T. Its residue vector is constant, 1 at the (4,9) point and −1/3 at each of the three bottom points. Thus E⁺/E_D is a trivial differential module K. Put φᵢⱼ=b^(i−1)T^(j−1)db/P_T, ξ=Tdb/b⁴, κ=Tdb/b⁵.

For a proper closed pair c_I dI+c_J dJ on C, write A_s=∇sΘ. Applying the differential to its lift in E_C⊗E⁺ gives the connecting class in H²(E_C⊗E_D):

    δΘ(c) = [c_J⊗A_I − c_I⊗A_J] dI∧dJ.

Indeed the Θ coefficient vanishes because ∇I c_J=∇J c_I. Replacing c by the gradient of a proper section changes this expression by a proper boundary, by flatness. In particular it vanishes on exact C pairs. With the fixed-T lift and the normalization db/P_T,

    A_J=φ₆₁,
    A_I=−(1/2)φ₅₁−6I⁵φ_(−3,4)
       =−(1/(2b)+6I⁵T³/b⁹)φ₆₁.

Substitution of 4I⁶T³=P_T−2b⁹T−(I/2)b⁸+Jb⁹ gives a lower-pole identity of literal relative forms

    I A_I=3φ₆₂+(I/4)φ₅₁−(3J/2)φ₆₁+(1/2)d_D(b⁻³).

For the C vector from α=p dy with p=1/τ, the acyclic lift has c_I=−e_y/2 and c_J=−e_τ in cohomology. The cup has an explicit absolute representative on the five-torus hypersurface G=J_D−J_C=0:

    dα∧dΘ=−dp∧dT∧dy∧db/(b⁴T)
          =d[−p dy∧db∧dT/(b⁴T)].

The simple-pole ambient numerator for this representative is −G_I/(b⁴T) in the volume order dI,dp,dT,dy,db. Its relative two-factor component is exactly c_J⊗A_I−c_I⊗A_J. The normalized physical source has nonzero cohomology on the full torus by the separate torus calculation. Independently localizing at further moduli divisors can change this comparison.

## Exact exclusion for arbitrary C coefficients on the three D sections

Consider the proper source σH with H=(I²/6)φ₅₂+2Iφ₉₁ and σ=−∇J²ω/12 in E_C. Allow arbitrary U,V in E_C⊗span_K{Θ,κ,ξ}, and test ∇I U+∇J V=σH. There are no bounds on their C coefficients, moduli denominators or derivative orders.

The two normal form formulas are

    φ₆₁=−ξ/6−(11I/36)φ₅₂+(J/2)φ₆₂−(2/3)φ₉₁,
    φ₅₁=−κ/18−(11I/36)φ₄₂+(J/2)φ₅₂−(2/3)φ₈₁.

For their literal relative primitives put m=3,4, i=9−m and s=Tdb/b^(m+1). On the quartic,

    (3−2m/3)s=(2/3)d_D(T/b^m)−6φ_(i,1)−(11I/6)φ_(i−1,2)+3Jφ_(i,2)−4φ_(i+3,1).

Also ∇Jξ=φ₆₂ and ∇Jκ=φ₅₂, and the I derivatives in relative cohomology are

    I∇Iξ=−2ξ−(I/6)φ₅₂−2φ₉₁,
    I∇Iκ=−8κ/3−(I/6)φ₄₂−2φ₈₁.

The coordinates ξ,κ,φ₄₂,φ₅₂,φ₆₂,φ₈₁,φ₉₁ are independent in proper D. For detail φ₄₂ has its only pole of order three at b=s⁴,T=c s⁹(1+O(s⁵)), c⁴=−I⁻⁶. Its Serre pairing with φ₅₂ is 1/(2I⁶), and its pairings with φ₃₃ and φ₄₃ vanish. At this place ξ,κ have pole orders four and eight. At b=s⁻²,T=c' s⁻⁹(1+O(s⁹)), (c')²=−I⁻⁶, ξ,κ have pole orders four and two. At all other toric points they are regular, and positive corrections in these two expansions cannot yield a residue in either form. The pairing of ξ with φ₃₃ is −2/I⁶, and its pairing with φ₄₃ is zero. The pairing of κ with φ₄₃ is −4/(7I⁶)−2/I⁶=−18/(7I⁶). Here the pairing convention is ΣRes((∫s)φ). These three diagonal entries prove independence modulo the holomorphic subspace. The last four displayed Newton forms comprise four different members of its basis. Finally Θ is independent of all seven by its nonzero residues.

Let r and a denote the Θ and κ coefficients of U. In the φ₄₂ and φ₈₁ coordinates nothing survives except

    (−11I/144)r−a/6=0,        −r/6−2a/I=0.

Their coefficient matrix has determinant 1/8, hence r=a=0. The Θ coordinate forces its coefficient s in V to satisfy ∇J s=0, hence s=0 by the rational-pencil argument below. We are left with U=uξ, V=vξ+cκ. The φ₉₁,φ₆₂ and φ₅₂ coordinates then force

    u=−I²σ,      v=0,      c=0.

The ξ equation becomes −I²∇Iσ=0. This is impossible. Both individual covariant derivatives ∇I and ∇J have zero kernel on E_C(K). For fixed generic I the smooth genus-four curves form the pencil J=−(1+y⁶)p³−yp²/2−Iyp/2 on the rational (p,y)-surface. For fixed generic J the equation can likewise be solved rationally for I on yp≠0. In each direction resolving the pencil gives a smooth projective rational surface, so H¹ of this total surface vanishes. The global invariant cycle theorem gives zero invariant H¹ of the fibres. A rational horizontal section would give such an invariant after restricting the base to a suitable nonempty open. One may embed the other transcendental parameter field in ℂ to apply this argument. Since ω is a nonzero holomorphic differential, ∇I∇J²ω≠0. [Deligne, Théorie de Hodge II, théorème 4.1.1](https://www.numdam.org/articles/10.1007/BF02684692/)

Thus the three D sections, with arbitrary proper genus-four coefficient vectors, cannot integrate the physical tensor. The connecting-class equation modulo *arbitrary additional proper D currents* remains open.

## Detection of the extension even along the J line

At fixed generic I, the total punctured D over a sufficiently small algebraic J-open is the torus (ℂ*)² with finitely many fibres of j_D removed. The polynomial j_D−a is irreducible for every finite a since the quartic at b=0 has its sole lower Newton edge of slope −9/4. All roots have valuation 9/4 and the degree of any factor is divisible by four. The toric points form marked sections after finite constant extension, and the smooth compactified family with its boundary marks is topologically locally trivial after deleting the exceptional levels. Leray gives H¹(total)→H⁰(base,R¹) surjective because the noncompact base curve has H²=0. The cohomology H¹(total) is spanned by dlog b, dlog T and the meridians dlog(j_D−a) of the removed fibres. This follows by removing the finitely many singular points of those irreducible curves, applying the Gysin sequence to their smooth loci, and using the displayed logarithms as meridian lifts. The vertical logarithms vanish on the fibre. Thus any J-horizontal rational class on the punctured fibre is a linear combination of the two toric logarithms.

A proper J-primitive f of φ₆₁ would make Θ−f horizontal. No combination of dlog b and dlog T has this residue vector. In fact the three bottom valuations force the coefficient of dlog T to be −1/3 and the (−2,−3) valuation forces the coefficient of dlog b to be 1/2. At (−2,−9) this would give 2 whereas the actual residue is zero. Thus the extension already fails to split in the J direction, despite its explicit logarithmic parent.

## A provably nonzero input to the connecting map

The rational-pencil injectivity on C also gives

    H¹_dR(K,E_C) ≃ ker(∇I : E_C/∇J E_C → E_C/∇J E_C),
    [c_I dI+c_J dJ] ↦ [c_J].

Flatness makes ∇I well defined on the quotient. An element of the kernel has ∇I c_J=∇J c_I for some c_I, which gives surjectivity. If c_J=∇J f, then c_I−∇I f is J-horizontal and vanishes, which proves injectivity. The same conclusion holds after exchanging I and J. In particular any closed C pair with c_J=∇J²ω is exact and has zero connecting class, even when unrestricted additional proper D currents are admitted.

The canonical pair from α is a nonzero element of this domain. To see this, fix I transcendental over ℚ. Every finite j_C=j₀ fibre is irreducible on the (y,p) torus. For j₀≠0 a reducible primitive cubic in p has a rational root c/g(y) with c a nonzero constant and g a monic divisor of 1+y⁶. Clearing denominators gives

    c³(1+y⁶)+(c²/2)yg+(Ic/2)yg²+j₀g³=0.

Only deg g=2 permits the largest degree to cancel. Write g=y²+a y+b. Its coefficients are algebraic numbers because its roots are among the fixed roots of 1+y⁶. The coefficients of y⁶, y⁵ and y⁴ force j₀=−c³, I=6ac² and b=a². The coefficient of y³ is then c²/2+2a³c³, forcing c=−1/(4a³) and I algebraic, a contradiction. For j₀=0, removing the torus unit p leaves a quadratic with discriminant y²/4−2Iy(1+y⁶), of odd valuation at y=0. Hence all removed fibres are irreducible on this torus.

The same Leray and meridian argument as for D shows that all J-horizontal rational classes on the punctured C are combinations of dlog y and dlog p. At each of the six boundary points p=∞, y=a, a⁶=−1, put τ=1/p. The fibre equation gives y=a−τ/(12a⁴)+O(τ²), so α=dy/τ has residue −1/(12a⁴). These numbers differ among the six points. Both torus logarithms have constant residue across those six. Thus α−f cannot be horizontal for a proper f. In particular ∇Jα=−e_τ has no proper J-primitive, and its closed pair is genuinely nonzero in H¹_dR(K,E_C). Its image under δ has the explicit representative above. These single-variable arguments do not decide whether that image equals the protected class after all proper mixed currents are allowed.

## Complete toric C inputs and the protected character

Write F=J+(1+y⁶)p³+yp²/2+Iyp/2. Consider five top-edge differentials

    ν_k=y^(k−1)p² dy/F_p=y^(k−1)ω/τ,       1≤k≤5.

At p=∞, y=a, a⁶=−1, the leading terms F_p=−(a/2)p+O(1) and dy=−dτ/(12a⁴)+O(τ)dτ give residue a^(k−6)/6. At y=0 all five forms are regular. At y=∞, take y=s⁻¹, p=c s²(1+O(s)), c³=−J; their orders are 5−k, hence they are again regular. At finite branch points regularity follows from dy/F_p=−dp/F_y on a smooth fibre. Their five residue characters on the six top points are independent modulo uniform values. By the meridian proof the five proper closed pairs [∇ν_k] are independent over the constants. At fixed y their coefficients are explicit:

    c_J=y^(k−1)(p²F_pp−2pF_p)dy/F_p³,
    c_I=(yp/2)c_J−y^k p²dy/(2F_p²).

These five exhaust the input classes from rational C parents with only toric residues. Over algebraically closed constants the y=0 edge and the y=∞ edge each form a transitive triple after descent to K, as their leading roots satisfy c³=−J. A horizontal residue vector therefore has one constant value on each triple and arbitrary constant values at the six fixed p=∞ marks. The single sum-of-residues equation leaves dimension seven. The two independent vectors from dlog y and dlog p give parents with zero derivative. After subtracting these and the ν_k any parent with horizontal toric residues is proper, hence has exact connecting input. This argument classifies the toric-parent subfamily.

In fact F=0 gives the literal holomorphic gauge α+ν₂/2=−I e_y−3J e_τ because F_p+yp/2=−I y−3J/p. The μ₆ symmetry isolates this pair for the protected form. Let ε⁶=1 and act by

    (I,J,y,p,T,b) ↦ (εI,ε³J,εy,εp,ε³T,ε⁻²b).

Both J_D and J_C transform by ε³. The D lift Θ is invariant. The C section ν_k has character ε^k, whereas the protected Laurent representative χ in the five-variable calculation has character ε². Indeed its two numerator terms both have character ε, its ordinary five-volume has character ε⁴, and G³ has character ε³. The connections and residue exact sequence are natural for this action. Projection onto the ε²-character over algebraically closed constants therefore retains only ν₂. Consequently within the entire toric C logarithmic-parent family, an equality after arbitrary proper correcting currents must take the form

    [physical]=c δΘ([∇α]),    c constant.

The scalar multiple is the only candidate in this family; the equality in proper mixed cohomology remains undecided.
