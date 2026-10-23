# Parity-correct CM kernel jets and their actual density remainder

These are actual rational currents on the stated finite source field. They
retain the full physical normalization. Their remaining density derivative
has **not** been cancelled by a mixed c/E2 current. They are not a
certificate or a completed primitive.

The constant field is a fixed field k of characteristic zero containing the
displayed roots of unity and constants; k=C gives the full certificate
contract. The arithmetic identities below are defined over the corresponding
number field.

## Source and elliptic coordinates

Use the complete field in
`../horizontal-cm/K3-ELLIPTIC-CORRESPONDENCE.md`. Its coefficients are

    C=c^6,
    H=1+c^-6*Y^-2+h^6,
    B=c*V*(T/2+h/3)+h*T*V^2/(2*c*Y),
    w^3=1+T^6, V^2=e/w, Y^2=1-e^3.

The physical cubic and source are

    f=C*p^3+B*p+H=0, g=B+3*C*p^2,
    R=B*p/g^3, source=R*Omega.

Scale the first elliptic factor to

    E1: y1^2=x1^3-16,
    x1=2^(2/3)*w^2/T^2, y1=2*(T^6-1)/T^3,
    eta1=dx1/(2*y1)=a_scale*dT/w,
    a_scale=2^(-1/3).

Adjoin k with k^3=H and put x=-4*k/(c^2*p). The normalized cubic
Galois elliptic curve is

    E3: y^2=x^3-16, eta3=dx/(2*y),
    B/(c^2*k^2)=(x^3-64)/(4*x^2).

The second elliptic form remains eta2=de/(2*Y). In these conventions

    Omega=-c^4/a_scale * dc^dh^eta1^eta2,
    R=-64*x^3*(x^3-64)/(c^6*H*(x^3+128)^3).

All derivatives of B,H,C and the finite-cover functions are retained.
In particular, this is not integration of the elliptic density alone.

## Kernel and the odd normal jets

Let zeta^2+zeta+1=0 and L=(x1-x)*(x1-zeta*x). A CM diagonal kernel
P satisfies dP=x*eta1^eta3. Its parts under
sigma3:(y,eta3)->(-y,-eta3) can be chosen as

    Pminus=-zeta^2*y*(x1+zeta^2*x)/L * eta1
           -x*y1/L * eta3,
    Pplus =-zeta^2*y1*(x1+zeta^2*x)/L * eta1
           -x*y/L * eta3.

They obey dPminus=x*eta1^eta3 and dPplus=0. The bare primitive is
odd under sigma3, whereas the physical source is even. Multiplying by
the odd coefficients gives two even first jets,

    alpha0=y*Pminus=A0*eta1+Bdx*dx,
    alpha1=y1*Pplus=A1*eta1+Bdx*dx,
    A0=-zeta^2*(x^3-16)*(x1+zeta^2*x)/L,
    A1=-zeta^2*(x1^3-16)*(x1+zeta^2*x)/L,
    Bdx=-x*y1/(2*L).

Thus they are rational without adjoining y. Exactly,

    d alpha0=C0*eta1^dx,
    d alpha1=C1*eta1^dx,
    C0=x*(x1+2*zeta^2*x)^2/(2*L),
    C1=-3*x1^2*x/(2*L),
    alpha0-alpha1=(zeta^2*x1^2-x^2)*eta1,
    C0-C1=2*x.

The paired difference cancels the CM graph poles. Each separate jet
retains them; cancelling those poles does not cancel the physical density
correction.

## Complete physical normal derivative

At fixed c and fixed points of E1 and E2, write

    b1=B_h=c*V/3+T*V^2/(2*c*Y),
    J=H*b1-4*B*h^5,
    x_h=4*x^3*J/[c^2*H*k^2*(x^3+128)],
    m=c^4*R/(2*a_scale*x*x_h)
     =-8*k^2*(x^3-64)/[a_scale*x*(x^3+128)^2*J].

The complete h derivative acts by

    D_h=partial_h+6*h^5*partial_H+b1*partial_B
        +(2*k*h^5/H)*partial_k+x_h*partial_x,
    D_h(b1)=0,
    J_h=2*h^4*(h*b1-10*B),
    m_h=m*[(3*x^2/(x^3-64)-1/x-6*x^2/(x^3+128))*x_h
           +4*h^5/H-J_h/J].

This is a nonzero rational derivative, not a derivative taken with H or
B artificially fixed. Let the subscript 1 denote the complete eta1-dual
physical derivative at fixed c,h,E2. Define the actual three-currents

    Gamma_i=m*alpha_i^dc^eta2.

Their full divergences, relative to Omega, are

    div Gamma_i=(C_i/(2*x))*R
       -a_scale/c^4 * [m_h*(A_i+Bdx*x_1)-m_1*Bdx*x_h].

The terms x_1 and m_1 include all first-factor derivatives of the actual
coefficient B. They have not been discarded. Pairing yields the simpler
actual current and explicit gap

    Gamma=m*(zeta^2*x1^2-x^2)*eta1^dc^eta2,
    d Gamma=[R-a_scale*(zeta^2*x1^2-x^2)*m_h/c^4]*Omega.

The first term is the immutable source with its exact normalization. The
second is the remaining physical density derivative. No mixed c/E2
correction cancelling it has been found. Treating m as constant would
incorrectly assert a primitive.

## Normalized root traces

At fixed physical p, changing k to zeta*k changes x to zeta*x. Put

    s=x^3=-64*H/(c^6*p^3), Q=x1^3,
    m0=m/x=-c^4*p^2*(s-64)/[2*a_scale*(s+128)^2*J].

The normalized k-root trace of each Gamma_i is

    Gamma_i_bar=m0*Zi^dc^eta2,
    Z0=s*(s-16)/(Q-s)*eta1-x1*y1/(6*(Q-s))*ds,
    Z1=s*(Q-16)/(Q-s)*eta1-x1*y1/(6*(Q-s))*ds.

Their differentials are

    dZ0=(Q-6*s+32)/(6*(Q-s))*eta1^ds,
    dZ1=-(5*Q-32)/(6*(Q-s))*eta1^ds.

The individual traced currents retain the actual CM graph pole Q-s.
Their difference is -m0*s*eta1^dc^eta2; the graph poles again cancel.
Since s=-64H/(Cp^3), this is the explicitly rational physical current

    Gamma_bar=-c^4*B*H*p/(2*a_scale*g^2*J)*eta1^dc^eta2.

The normalized trace in the cubic field satisfies

    Tr_normalized(p/g^2)=-3*H/Delta,
    Delta=4*B^3+27*C*H^2.

Consequently its tracefree projection is

    -c^4*B*H/(2*a_scale*J)
      *(p/g^2+3*H/Delta)*eta1^dc^eta2.

This projection retains two-component cubic data. Subtracting the field
trace also subtracts the differentiated trace current; it does not remove
the tracefree remainder. All finite-cover currents can be descended by
normalized trace only after the complete source equation has been solved.

## Actual coupled coefficient current

The tracefree paired current can be placed directly in the complete
canonical gauge

    Vcanonical=-H/(p*g)-1/3, Wcanonical=C*H*R,
    kappa=B^3/(C*H^2).

The exact cubic-field identity

    p/g^2+3*H/Delta
      =-27*H/(2*Delta)*Vcanonical-2/(C*H)*Wcanonical

shows that neither component was lost in this construction. As base
vector currents relative to the actual Omega, the only nonzero components
are in the h direction:

    a=-27*B*H^2/(4*J*Delta), d=-B/(C*J),
    lambda_h=D_h(log kappa)=3*J/(B*H).

The full remaining coefficient equations are explicitly

    residual_V=D_h(a)+3*lambda_h*d/(4*kappa+27),
    residual_W=D_h(d)-2*lambda_h*a
        +(27-2*kappa)*lambda_h*d/(4*kappa+27)-1/(C*H).

Both are nonzero, with every h derivative of H and B retained. For an
actual physical check, take c=h=T=V=1, Y=i and w^3=2. These satisfy
the finite-field relations and give H=C=1, B=5/6-i/2 and b1=1/3-i/2.
Both displayed residuals are nonzero at that specialization. The full
two-component data and exact residual expressions are stored in
`paired-canonical-current-results.json`. This supplies a precise input
for a possible mixed correction rather than an assertion that one exists.

`odd_kernel_jets.py` verifies 28 exact kernel, parity, first-jet and
root-trace identities. `physical_normal_jets.py` verifies six exact normal
normalization and cubic-trace identities. `paired_canonical_current.py`
verifies six exact canonical-current and actual nonzero-remainder checks.
These local algebra checks do
not assert a completed mixed correction or a Lean-checked certificate.

The independent full compact scalar-adjoint reconstruction in
`../../../coupled-fresh/rank4-relative/SCALAR-HORIZONTAL-CLOSURE.md` is a
separate possible correction mechanism. No map solving its forced scalar
equation with the remaining density derivative is claimed here.

## Subsequent mixed normal homotopies

The original forty checks above were independently audited with seventeen
exact Fraction groups in
`../../../audit/cubic-ray/ODD-CM-JETS-AUDIT.md`. The physical source sign,
root-trace factors and nonzero full residual were confirmed.

The next constructive calculation is
`mixed-independent/PROJECTOR-PARTITION.md`. A polynomial-normalized cubic
sheet projector supplies an actual rational logarithmic current with its
full d lambda terms retained. The source-guided three sections
lambda_i=-H_i/H, H_i=1,Z^-2,h^6 cancel those mixed terms exactly. A complete
deck-balanced c/E2 residue is rational in the physical coordinates:

    beta0=d(u/v)^d(Zv^2).

The resulting current retains both canonical components. Its remaining
source is explicit and has a nonzero V component at an actual physical
point, so this finite homotopy does not close the target. Thirty-three
additional exact checks verify the normalizer, actual current, all mixed
derivatives, physical residue and remaining forcing.

`mixed-independent/MIXED-COMPLETION.md` separately records an exact-kernel
dF residue completion. Modulo an exact current it lies in the already
excluded pure-component/horizontal scope; standalone inversion of that
particular completion was stopped. This limitation does not exclude the
full coupled mixed-current problem.
