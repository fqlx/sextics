# A precise Hodge-subquotient reduction for the raw CI

This lemma gives the conditional global argument without requiring every
individual connecting-map rank. Its geometric input (the complete list of
normalized conductor and exceptional curves) is not yet established here.

Let X be the proper raw CI, with H¹(O_X)=0 as verified in cohomology.py.
Let Xr be its reduction, N the disjoint normalization of Xr, and D the
preimage in N of the conductor subscheme. Let S be a resolution of N.
For the main-component resolution, use its direct summand in S.

The abelian part of Pic⁰(Xr) is zero. One can pass from X to its reduction
without losing an abelian Picard factor: for a square-zero thickening,
the obstruction to lifting line bundles lands in an additive H² ideal
cohomology group. If G is the reduced connected Picard group downstairs
and L its maximal connected affine subgroup, mod out the obstruction
target by the image of L. The induced homomorphism from the abelian
quotient G/L to that affine quotient is zero. Hence the kernel of the
obstruction still surjects onto G/L, so an abelian factor cannot be lost.
Induct on the nilpotent ideal. On the other hand H¹(O_X)=0 makes the
tangent space of Pic⁰(X) zero. Thus no abelian Picard factor can occur on
Xr. This argument does not assume that an abelian quotient of a possibly
nonproper Picard group embeds as a subgroup.

The conductor square is a finite pushout. A line bundle on N trivial on
D glues with the trivial bundle on the conductor downstairs, so the
kernel of Pic(N)->Pic(D) comes from Pic(Xr), apart from gluing units.
On abelian parts this gives a homomorphism with finite kernel

    Pic⁰(N) -> product Jac(normalizations of the reduced curves in D).

Indeed the remaining parts of Pic⁰(D) are affine (toric or unipotent), and
there is no nonconstant group homomorphism from an abelian variety into
an affine algebraic group. Equivalently, rational weight-one Hodge
structures of N are subquotients of those of the normalized conductor
curves. Scheme multiplicities affect affine Picard parts but do not add
new simple abelian factors.

Normal projective surfaces have isolated singularities. For their
resolution, connected fibers and the Leray sequence give

    0 -> H¹(N,Q) -> H¹(S,Q)
      -> direct_sum H¹(exceptional fibers,Q) -> H²(N,Q).

The weight-one parts of the exceptional fibers come from Jacobians of
the normalizations of their curve components; their dual graphs add only
weight-zero terms. Therefore every simple abelian factor of Pic⁰(S) is
a factor of a normalized conductor curve or an exceptional curve.

All constructions can be made equivariant for U->-U. The same conclusion
then holds character by character. In particular, if the odd normalized
conductor/exceptional Jacobians contain only the CM elliptic isogeny
class and the independently excluded residual factors, no simple factor
of the genus11 boundary Jacobian can occur in the restriction image
H¹(S)_odd -> H¹(C)_odd. Polarizable weight-one Hodge structures are
semisimple, so absence of the relevant simple factors forces that image
to vanish.

This does not prove that the entire irregularity is zero, that every
global form is detected by C, or that the original Hodge class vanishes.
The remaining essential input is exhaustive geometric control of D and
the exceptional fibers, including interior isolated singularities and
corner intersections. The local models currently listed in
boundary_inventory.md are not yet that exhaustive proof.
