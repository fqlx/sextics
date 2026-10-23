# An explicit finite K3 and elliptic-product source correspondence

This is a source-retaining finite correspondence, not a primitive. In
particular it does not replace the full source by a polynomial or invariant
density on a product of elliptic curves.

Use the constant-density chart from `../poisson/CONSTANT-DENSITY-CHART.md`:

    H=1+Z^-2+h^6, C=Z^2+u^6+v^6,
    B=u/2+hv/3+huv/(2Z),
    Omega=-(1/3)dZ dh du dv,
    R=Bp/(B+3Cp^2)^3, f=Cp^3+Bp+H=0.

All function fields use a fixed characteristic-zero constant field k, with
k=C for the full certificate contract. Adjoin c with c^6=C and normalize

    Z=c^3 Y, u=c U, v=c V,
    Y^2+U^6+V^6=1.

For a fixed nonzero c this is the affine chart of the isotrivial double-sextic
K3 surface. Its holomorphic two-form is dU dV/Y. Put T=U/V and adjoin w with
w^3=1+T^6. Define e=wV^2. The common finite function field has relations

    w^3=1+T^6, Y^2=1-e^3, V^2=e/w, U=TV.

Its two fixed elliptic factors are

    E1: y1^2=e1^3-4,
    e1=w^2/T^2, y1=(T^6-1)/T^3,
    eta1=de1/(2y1)=dT/w;

    E2: Y^2=1-e^3,
    eta2=de/(2Y).

The differential identity is exact:

    dU dV/Y = dT de/(2wY) = eta1 eta2.

The common field is finite over both the K3 and the elliptic product.
Over the normalized K3 it is obtained by adjoining w, so its degree is at
most three. Over the elliptic product, an explicit inverse construction is

    b^2=e1,
    T^3=(y1+b^3)/2,
    w=bT,
    V^2=e/w,
    U=TV.

Thus its degree is at most twelve. These are upper bounds; no equality of
function fields or rational parametrization of the K3 is asserted. They
suffice for a finite correspondence and normalized-trace descent of any
completed current on the common field. All maps are taken on their generic
open sets, where the displayed denominators are nonzero.

The complete physical four-form and source on this field are

    Omega=-c^4 dc dh eta1 eta2,
    R Omega=-c^4 R dc dh eta1 eta2
           =-W/(c^2 H) dc dh eta1 eta2,
    W=CH R.

The full coefficient functions are retained:

    C=c^6,
    H=1+c^-6 Y^-2+h^6,
    B=cV(T/2+h/3)+hT V^2/(2cY),
    V^2=e/w.

H is independent of the first elliptic factor. B generally varies along
both factors, and H varies along the second. Their derivatives, as well as
all derivatives of c and h, remain part of the actual source-current
equation. Factoring the K3 differential does not supply scalar primitives
for R or cancel the physical correction terms.

For comparison with a Fermat first-factor calculation, adjoin sqrt(w) and
set a1=T/sqrt(w), b1=1/sqrt(w). Then

    a1^6+b1^6=1, da1/b1^5=eta1,
    B=A a1+D b1+E a1b1,
    A=c sqrt(e)/2, D=ch sqrt(e)/3, E=he/(2cY).

The factorization B+AD/E=(E a1+D)(b1+A/E) is an algebraic identity; it is not
an integration argument.

The normalized trace also retains the complete product. Under c -> zeta6 c,
the physical variables are fixed by Y -> zeta6^-3 Y, V -> zeta6^-1 V,
e -> zeta6^-2 e, while T,w and eta1 are fixed. The character of eta2 is +1,
which cancels the character +5 of c^4 dc. Under w -> zeta3 w at fixed
T,Y,V, one has e -> zeta3 e, eta1 -> zeta3^-1 eta1 and
eta2 -> zeta3 eta2. Both physical coefficient functions and the complete
four-form remain invariant. An isolated elliptic factor can have zero trace;
the balanced product displayed here does not have that character defect.

## A monic cubic with polynomial radial density

The exact further substitution a=ch, q=c^4p, multiplying f by c^6, gives

    fnew=q^3+Btilde*q+S,
    S=c^6+a^6+Y^-2,
    Btilde=alpha*c^3+beta*a*c^2+gamma*a,
    alpha=TV/2, beta=V/3, gamma=TV^2/(2Y).

The elliptic coefficient functions satisfy

    gamma=3alpha*beta/Y,
    64alpha^6+729beta^6=1-Y^2.

The actual scalar residue does not change:

    Rnew=Btilde*q/(3q^2+Btilde)^3=R.

Both the residue and the unreduced double-pole form have their complete
radial density retained:

    source=-c^3 Rnew dc da eta1 eta2,
    five-form=-c^3 q^2/(2fnew^2) dc da eta1 eta2 dq.

This is an actual polynomial radial density obtained from the immutable
source. It is not an appeal to universal polynomial-density integration:
alpha,beta,gamma,Y still vary along the elliptic factors. Their derivatives
remain necessary in a joint current. `radial_polynomial_source.py` checks
twelve exact coefficient, canonical-gauge, residue and five-form identities.

The canonical kappa,V,W gauge itself is unchanged by this transformation:

    kappa=Btilde^3/S^2,
    V=-S/[q(3q^2+Btilde)]-1/3,
    W=S Rnew.

Its complete source vector is now (0,1/S). In the commuting frame
partial_c,partial_a,delta1,delta2 dual to dc,da,eta1,eta2, the actual
divergence is

    div(X)=partial_c Xc+3Xc/c+partial_a Xa+delta1 X1+delta2 X2.

Here delta1=w partial_T and delta2=2Y partial_e, extended by the displayed
finite field relations. In particular delta1(S)=0, while
delta2(S)=6e^2/Y^3. For prospective full coupled currents A,D, every one of
these derivatives is retained in

    div A+3 D(log kappa)/(4kappa+27)=0,
    div D-2 A(log kappa)+(27-2kappa)D(log kappa)/(4kappa+27)=1/S.

This remains the complete rank-two current interface after the finite
changes. No component, divergence or coefficient derivative has been set
to zero.

## Full canonical section on the CM first-factor graph

For the physical constant-density variables u,v, put

    M=u^6+v^6, N=u^6v^6, Q=M^2/N.

The first elliptic coordinate has e1^3=Q. Identifying it with the normalized
cubic Galois elliptic coordinate X by X^3=4Q gives a selected graph sheet
with exact canonical values

    kappa=(Q-16)^3/(16Q^2),
    V=2(Q-16)/(3(Q+32)),
    W=-16Q(Q-16)/(Q+32)^3.

Both connection equations hold with theta=kappa d/dkappa. Clearing the
graph equation gives

    16NM^4 B^3-H^2 C(M^2-16N)^3=0.

This graph is formed from the actual K3 first elliptic factor, with its
correct differential. It differs from graphs indexed by the held-out
original X coordinates. The rational selected-sheet data are useful
residue inputs for a possible Gysin or normal-jet construction. Neither
the graph equation nor this selected-sheet evaluation identifies its Gysin image with
the immutable source. `k3_graph_section.py` checks seven exact identities.

`k3_elliptic_correspondence.py` verifies eighteen exact field, differential,
Jacobian and complete-source/character identities. The direct rational chart has its
own eleven exact checks. Neither file supplies a complete current, Lean
proof, or certificate.
