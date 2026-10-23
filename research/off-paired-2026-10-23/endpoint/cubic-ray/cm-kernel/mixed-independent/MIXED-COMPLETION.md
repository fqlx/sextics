# Closed kernel completion and the selected normalizer pole

This records exact source-carrying partial identities. No mixed current has
closed the full source. The first construction below reduces to the already
audited pure-component scope, so its standalone inversion has been stopped.
The second calculation identifies the actual CM normalizer pole for a
different idempotent-residue construction.

Use the full physical source and notation in `../ODD-NORMAL-JETS.md`, over
a fixed characteristic-zero constant field k; use k=C for the full contract.

## An actual mixed c/h completion of the odd kernel residue

The odd kernel satisfies

    dPminus=x eta1^eta3, eta3=dx/(2y).

For any odd rational function F, the actual three-current

    J_F=Pminus^dF^eta2

has closed graph residue, since it is a constant kernel residue times
`dF^eta2`. Its literal derivative is `dPminus^dF^eta2`; no coefficient
derivative has been omitted. In particular take F=4cym. Let

    U_c=partial_c-r partial_h,
    r=x_c/x_h=kappa_c/kappa_h,
    J=H B_h-4Bh^5,
    r=[H B_c-2BH/c-(2/3)B H_c]/J,
    ell=U_c(m)/m=(2/3)U_c(H)/H-U_c(J)/J.

The derivatives here hold the two actual elliptic points fixed and include

    H_c=-6(H-1-h^6)/c,
    B_c=B/c-2hE/c^2,
    (B_h)_c=B_h/c-2E/c^2,
    E=TV^2/(2Y).

The physical orientation gives

    dJ_F=(1+c ell) R Omega.

Thus the bad graph-pole residue derivative can be completed by a genuine
mixed c/h current, leaving the explicit normal density derivative `c ell R`.
It is not zero.

There is an essential scope limitation. Exactly,

    J_F=F dPminus^eta2-d(F Pminus^eta2).

For F=4cym its normalized root trace, modulo this exact current, is

    W*c^5 B/(3 a_scale C J) eta1^dlog(kappa)^eta2.

The corresponding rational base vector is

    D=c/(CH) U_c,
    D(log kappa)=0,
    div D=(1+c ell)/(CH).

It has only the W component. More generally every construction of the
displayed closed-`dF` kernel form is, modulo an exact current, a current
whose base three-form contains `d kappa`. Its base vectors are therefore
kappa-horizontal. A completed source equation in this family would give a
pure-W solution, in the scope already excluded by the independently audited
pure-component obstruction. This observation prevents using a merely
completed graph residue as an unsupported claim of full source closure.

`closed_kernel_completion.py` passes eight exact physical-current,
normalization, cubic-reduction and scope identities. The original kernel
and exterior orientation were checked separately in the parent calculation.

## The idempotent normalizer on the actual CM graph

For the distinct idempotent-residue construction, let

    u^3=lambda H/C, D=H+Bu+Cu^3,
    g_u=B+3Cu^2, kappa=B^3/(CH^2).

On the selected sheet D=0, the exact elementary identity is

    g_u*u=H(2lambda-1).

Hence the selected normalizer pole on the graph is only lambda=1/2.
Tracing all three u sheets gives

    Norm_u(g_u)=CH^2(kappa+27lambda^2),
    (kappa+27lambda^2)|D
      =(2lambda-1)(13lambda^2+5lambda+1)/lambda,
    kappa|D=-(1+lambda)^3/lambda.

The quadratic factor comes from the other two u sheets. It is not an
additional pole on the selected u sheet.

For the actual K3 first-factor graph, lambda=-64/x1^3. The standard
three-isogeny is

    E1: y1^2=x1^3-16,
    xprime=x1-64/x1^2,
    yprime=y1(1+128/x1^3),
    Eprime: yprime^2=xprime^3+432,
    kappa=(xprime/4)^3.

The selected pole lambda=1/2 is x1^3=-128, which maps to yprime=0.
These are preimages of target two-torsion points. The elliptic isogeny is
unramified; its x-coordinate map has a branch at these points. In
particular `4 kappa+27=yprime^2/16` on this graph.

Keeping the finite u extension while completing a current preserves the
distinction between its selected normalizer pole and the extra factors
introduced by taking the full norm. This can guide a source-compatible
normal correction, but supplies neither that correction nor an automatic
pole cancellation.

`normalizer_isogeny_factor.py` passes seven exact selected-sheet,
normalizer-norm and elliptic-isogeny identities.
