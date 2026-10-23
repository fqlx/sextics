# Independent audit of the parity-correct CM normal currents

The rational currents in
`endpoint/cubic-ray/cm-kernel/ODD-NORMAL-JETS.md` have the stated physical
normalization and retained correction. No sign or normalized-trace error was
found. This is a genuine partial current, not a completed primitive.

`verify_odd_cm_jets_fraction.py` passes 17 exact groups, using only
standard-library Fraction arithmetic. It independently reduces the fixed
elliptic equations and `zeta^2+zeta+1`, clears the kernel denominators,
computes all three normalized root pullbacks, and computes the cubic trace
from an explicit inverse and Newton sums. No primary SymPy code is imported.

## Kernel and physical orientation

The two kernel derivatives, rational even jets, cancellation of the graph
poles in their difference, and `C0-C1=2x` all pass exact polynomial checks.
The rescaled first elliptic differential is

    eta1=2^(-1/3) dT/w=a_scale dT/w.

Consequently the physical volume established by the K3 correspondence is

    Omega=-c^4/a_scale dc wedge dh wedge eta1 wedge eta2.

For `alpha_i=A_i eta1+Bdx dx`, write

    dx=x_h dh+x_1 eta1+(terms in dc,eta2).

Since the omitted terms wedge to zero with `dc wedge eta2`, direct exterior
differentiation of `Gamma_i=m alpha_i wedge dc wedge eta2` gives

    dGamma_i = [m_h(A_i+Bdx x_1)-m_1 Bdx x_h-m C_i x_h]
               dc wedge dh wedge eta1 wedge eta2.

Dividing by the negative physical volume gives exactly the primary formula

    div Gamma_i = (C_i/(2x)) R
      -a_scale/c^4 [m_h(A_i+Bdx x_1)-m_1 Bdx x_h],

when `m=c^4 R/(2 a_scale x x_h)`. This derives the sign independently and
shows why the complete first-factor derivatives cannot be dropped.
Subtracting the jets cancels `Bdx`, giving the stated paired current and gap

    Gamma=m(zeta^2 x1^2-x^2) eta1 wedge dc wedge eta2,
    dGamma=[R-a_scale(zeta^2 x1^2-x^2)m_h/c^4] Omega.

## Complete physical h derivative and nonzero gap

The complete coefficients have `H_h=6h^5`, `C_h=0`, `B_h=b1`, `b1_h=0`.
Differentiating `k^3=H` and

    B/(c^2 k^2)=(x^3-64)/(4x^2)

gives

    k_h=2kh^5/H,
    x_h=4x^3 J/[c^2 H k^2(x^3+128)],
    J=H b1-4Bh^5,
    J_h=2h^4(h b1-10B).

Substitution into the source normalization gives
`m=-8k^2(x^3-64)/(a_scale x(x^3+128)^2 J)`. Ordinary quotient
differentiation gives the displayed logarithmic expression for `m_h`; none
of `H,B,k,x` is artificially fixed.

There is a particularly simple exact nonzero witness on the actual common
field:

    c=1,h=0,T=0,w=1,e=-2,Y=3,V^2=-2,
    H=10/9,B=0,b1=V/3,k^3=10/9,x=4.

Here `J=10V/27` is nonzero. Although `m=0`, differentiating its factor
`x^3-64` gives

    a_scale m_h=-1/320.

Thus `m_h` is not the zero rational function. This point is regular in the
common `T,w,e,Y,V` field chart; `x1` has a pole at `T=0`. The specialization
is used to certify the field function `m_h`, not as a finite numerical value
of the full paired current at an `x1` pole.

## Normalized traces and canonical coefficients

The k-root pullback fixes physical `p` and sends `x` to `zeta x` and `m`
to `zeta m`. The independent calculation includes the separate pullback
factor on `dx` and the division by three. It verifies both `Z_i` forms, their
derivatives, and their difference. No root-trace factor is missing.

The paired root trace is the stated physical rational current. Its reduction
in the cubic field is checked after clearing the actual cubic relation.
Independently,

    g^(-1)=(4B^2-9CHp+6BCp^2)/(4B^3+27CH^2)

modulo `Cp^3+Bp+H`. Newton sums through the fifth power give

    Tr_normalized(p/g^2)=-3H/(4B^3+27CH^2).

The tracefree projection and its exact two-component identity therefore
agree. Converting the three-form to a vector current uses

    i_(j partial_h)Omega=-c^4/a_scale*j eta1 wedge dc wedge eta2,

so its two h-components have precisely the primary signs

    a=-27BH^2/(4J Delta), d=-B/(CJ).

Because the physical volume density depends only on `c`, their divergences
use the ordinary complete h derivative. The full two canonical residuals,
including both connection couplings, were independently evaluated in Q(i)
at the actual point `c=h=T=V=1,Y=i,w^3=2`. Both are nonzero; exact rational
complex values are stored in `odd-cm-jets-fraction-results.json`.

Normalized trace commutes with the physical derivations in characteristic
zero. Subtracting the trace current also subtracts its derivative; it does
not cancel the remaining tracefree derivative. A mixed correction carrying
the full source, and the eventual finite-certificate transport, remain open.

No certificate has been found.
