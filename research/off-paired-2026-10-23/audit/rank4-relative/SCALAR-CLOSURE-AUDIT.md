# Independent audit of the complete compact scalar closure

The scalar equation in
`coupled-fresh/rank4-relative/SCALAR-HORIZONTAL-CLOSURE.md` is correct as an
equivalence for **all rational currents in the compact rank-four endpoint
module**, over the full physical finite coefficient field. It imposes no
one-flow, degree, or pole restriction within that module. No rational solution
of the resulting forced equation has been supplied.

`verify_scalar_closure_fraction.py` passes 50 exact audit groups. It uses only
Python's standard library and the independent audit polynomial arithmetic. It
does not import either primary verifier or SymPy. Its input connection hash is
recorded in `scalar-closure-fraction-results.json`.

## Physical source and coefficient derivations

In the original endpoint coordinates

    H=1+x^6+y^6+z^6+xyz/2,
    C=x^3 z/2+xy/3,
    J=H_x C_y-H_y C_x,

set `a=x^3` and `q=3C-3az/2`. Exact polynomial substitution gives

    q=xy,
    P=a^4+q^6+a^2(z^6+qz/2+1-H)=0,
    P_a=x^3 J.

Thus `phi=q^3/P_a=y^3/J` is precisely the original source density after the
physical `(x,y,z)` to `(H,C,z)` Jacobian. The three displayed derivatives of
`a` in the primary note are correct, and the audit checks their pairwise
commutators after clearing `P_a^3`. It also checks the full formula for
`D_H(phi)`, including `q_a` and the partial derivative `P_aH=-2a`.

The original compact source is `-phi ∇H(s0)/6`, using the established endpoint
residue orientation. Both source shifts are correct in all four cyclic rows:

    original = ∇H(-phi s0/6)+(D_H phi/6)s0,

    original = ∇C(C phi s0/(9H))
               -(C D_C phi/(9H))s0.

No derivative is taken while incorrectly fixing the physical variable `a`.

## Cyclic operator, order and reconstruction

Starting from the independently audited column connection data, the audit
recomputes `s_j=∇C^j omega0` through `j=4`, clearing a fixed denominator at
each derivative. All four companion coefficients, all sixteen entries of the
H-connection formula, and

    det(s0,s1,s2,s3)=-16533720 C^2 H^4/(4C^6-729H^4)^3

agree. The determinant is nonzero in the physical function field, so this is
a basis there. These statements use column connection conventions.

With `L=D_C^4-c3 D_C^3-c2 D_C^2-c1 D_C-c0`, its formal adjoint is

    L* f=D_C^4 f+D_C^3(c3 f)-D_C^2(c2 f)+D_C(c1 f)-c0 f.

The order of coefficient multiplication inside these derivatives is essential
and is as written. The independent checker verifies the reconstruction vector
with four arbitrary coefficient jets of `f`: its compact divergence is
`(-L*f,0,0,0)`. It then verifies all four rows after the arbitrary horizontal
terms `U,W` and the correction `v=t-eu`, `e=-2C/(3H)`, are included.

The denominator-free identity for `L*(C^2 Delta g)` also passes as an operator
identity on arbitrary commuting jets of `g`, rather than by testing finitely
many polynomial functions.

## Why this compresses arbitrary currents

For an arbitrary cyclic vector `b`,

    E(b)=b0-D_C b1+D_C^2 b2-D_C^3 b3,

and the primary `B(b)` satisfy the four exact identities

    b-E(b)s0=∇C B(b).

The independent arbitrary-jet calculation verifies the stronger direct
compression formula for unrestricted columns `u,v,w`:

    E(∇H u+∇C v+D_z w)
      =-L*(v3+e u3)+T E(u)+D_z E(w),
    T=D_H+(2C/(3H))D_C.

Consequently every full compact solution gives a scalar solution with

    f=v3+e u3, U=E(u), W=E(w).

Conversely the primary explicit reconstruction turns every scalar solution
into all four compact current rows. This is a two-way reformulation; the
arbitrary horizontal functions have not been set to zero or constrained to a
single physical flow. Flatness also gives the explicit replacement

    u'=E(u)s0,
    w'=E(w)s0,
    v'=v+∇H B(u)+D_z B(w),

which preserves the original divergence and has `v'_3=v3+e u3`.

## Literal transport and precise scope

The displayed recurrence for the exact fiber primitive is correct:
differentiating `A/Z` gives
`(D_C A-A f_C/(2f))/Z`, and the stored Dwork primitives contribute
`sum T_k R_(C,k)`. Thus higher cyclic derivatives keep their exact fiber
corrections. A solved scalar equation would still need those corrections,
the actual source-carrying finite-certificate transport, homogeneous legal
denominator clearing, and the required kernel verification.

This equivalence covers the complete **compact rank-four module**. It does
not assert that every rational differential on an endpoint fiber has no
moving-pole or residue contribution. The separately constructed infinity and
finite moving-pole modules remain valid additional possibilities. The scalar
closure therefore supplies a positive construction interface, without an
unrestricted nonexistence claim if any smaller scalar ansatz fails.

No certificate has been found.
