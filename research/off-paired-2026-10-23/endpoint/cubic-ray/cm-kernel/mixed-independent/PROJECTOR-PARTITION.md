# Full projector current with a source-guided mixed partition

The finite normalizer and its full mixed derivatives check exactly. The
three actual H-summand sections cancel their mixed lambda terms, but their
remaining source does not equal the immutable forcing. In particular a
nonzero V component remains. No certificate or completed primitive is
claimed.

Fix a characteristic-zero constant field k; use k=C for the full contract.
All traces below are normalized. The function-field formulas are defined
over Q and pass to k without changing their identities.

## Finite polynomial normalizer and actual current

Start with

    f(p)=Cp^3+Bp+H=0, Delta=4B^3+27CH^2,
    u^3=lambda*H/C, D=H+Bu+Cu^3,
    Q=C(p^2+pu+u^2)+B,
    I(u)=(4B^2-9CHu+6BCu^2)/Delta,
    e_star=Q*I(u)-1/3.

The exact identity is

    (B+3Cu^2)*I(u)-1
      =9C(2Bu-3H)*D/Delta.

Thus e_star has the same projector residue on D as Q/(B+3Cu^2)-1/3,
with values 2/3 and -1/3 on its selected and other cubic sheets.
The auxiliary normalizer poles B+3Cu^2 have been removed. The current
still has its actual logarithmic D pole, whose residue is retained.

Normalize p=(H/C)^(1/3)r, u=(H/C)^(1/3)v and
beta=B/(C^(1/3)H^(2/3)). Then

    r^3+beta*r+1=0, v^3=lambda, beta^3=kappa,
    d=D/H=1+lambda+beta*v,
    E=(r^2+rv+v^2+beta)(4beta^2-9v+6beta*v^2)/(4beta^3+27)-1/3.

Take the normalized v-root trace and the tracefree r-cubic projection of
the actual one-form E*dlog(D). Write the result as

    Theta=EH*dlog(H)+EK*dlog(kappa)+EL*dlambda.

Use the complete canonical basis

    V=-H/[p(B+3Cp^2)]-1/3,
    W=CH*Bp/(B+3Cp^2)^3,
    theta=kappa*nabla_kappa,
    theta(V)=-2W,
    theta(W)=[3V+(27-2kappa)W]/(4kappa+27).

Let t=4kappa+27 and N=(1+lambda)^3+kappa*lambda. The exact two-component
coefficients of the actual normalized current are

    EH=(4kappa-81lambda-54)/t *V-12(lambda+1)*W,

    EK=lambda(2kappa+3lambda^2-3lambda-6)/(6N)*V
       -lambda*t*(lambda+1)/(3N)*W,

    EL=(8kappa^2-378kappa*lambda+54kappa-486lambda^3
         -1458lambda^2-729lambda-486)/(6tN)*V
       -(28kappa*lambda+4kappa+36lambda^3+108lambda^2
         +54lambda+63)/(3N)*W.

The inverse of d used here is

    d^-1=[(1+lambda)^2-(1+lambda)beta*v+beta^2*v^2]/N.

The verifier checks this inverse after reduction modulo v^3-lambda in
every polynomial coefficient, not only after taking a trace.

## Full curvature, including d lambda

Put

    P=partial_lambda(EH)=-81V/t-12W,
    EH=V+(lambda+1)P,
    theta(P)=36(5kappa-27)V/t^2+6(4kappa-27)W/t.

Direct differentiation gives

    dTheta=theta(EH)*dlog(kappa)^dlog(H)
           +P*dlambda^dlog(H)
           +theta(P)*dlog(kappa)^dlambda,

    theta(EH)=36(5kappa-27)(lambda+1)V/t^2
       +2[(12lambda+8)kappa-81lambda-108]W/t.

The graph denominator N cancels from this derivative. Only the universal
discriminant factor t remains. No lambda derivative has been discarded.
For lambda depending only on E1, those derivatives vanish only after
wedging the complete current with eta1; the analogous statement holds for
lambda(E2) and eta2.

Modulo a **closed** one-form current, the actual Theta can be replaced by

    EH*dlog(H)-lambda*theta(P)*dlog(kappa).

This is a statement about equal derivatives; exactness of the discarded
closed current is not asserted. An additional elementary exact
differential rewrites that representative as

    V*dlog(H)+P[(lambda+1)dlog(H)+dlambda].

## Actual physical deck and mixed c/E2 completion

The bare two-form eta1^eta2 has c-root character +1. For invariant lambda
the universal Theta has character zero, so Theta^eta1^eta2 has normalized
c-deck trace zero. It cannot be identified with the physical source.

A complete invariant closed residue is

    betaS=eta1^d(c^5 eY)
      =eta1^[5c^4 eY dc+c^5(2-5e^3)eta2].

It is invariant under both the c and w decks. Moreover it descends
rationally to the constant-density coordinates:

    beta0=betaS/a_scale=d(u/v)^d(Zv^2)
      =(v du-u dv)^dZ+2Z du^dv,
    a_scale=2^(-1/3).

Indeed c^5eY=wZv^2 and eta1=a_scale*d(u/v)/w, while d(u/v)^dw=0.
The rescaled actual current Theta^beta0 therefore needs no CM-root
variables in its residue two-form. This beta0 is exact. No assertion that
an exact residue alone serves a nonzero H31 target is made.

For the physical chart

    H=1+Z^-2+h^6,
    C=Z^2+u^6+v^6,
    B=u/2+hv/3+huv/(2Z),
    Omega=-(1/3)dZ^dh^du^dv,

let X=Z*partial_Z-u*partial_u/2-v*partial_v/2. It has divergence zero.
For two physical one-forms xi,psi, define

    J(xi,psi)=6[xi_h*psi(X)-psi_h*xi(X)].

The exact physical source of Theta^beta0 is

    d(Theta^beta0)/Omega
      =theta(EH)*J(dlog(kappa),dlog(H))
       +P*J(dlambda,dlog(H))
       +theta(P)*J(dlog(kappa),dlambda).

This retains the genuine c/E2 correction terms from the complete residue.
It also retains both V,W components. For example,

    J(dlog(kappa),dlog(H))
      =-6[(X log kappa)*(6h^5/H)
           -(partial_h log kappa)*(-2Z^-2/H)].

## The three actual H-summand sections

Let H1=1, H2=c^-6Y^-2=Z^-2, H3=h^6 and take

    lambda_i=-Hi/H, sum_i lambda_i=-1.

These are source-guided cube sections: u_i^3=-Hi/C cancels exactly one
actual H summand in f(u_i). Use the same actual beta0 for all three
currents. Summing the full curvature before wedging cancels both mixed
terms, since sum_i d lambda_i=0. The remaining current, modulo a closed
current, is

    (3V+2P)*dlog(H)^beta0.

Its exact source is

    [72(5kappa-27)V/t^2+6(4kappa-81)W/t]
       *J(dlog(kappa),dlog(H))*Omega.

This finite mixed cancellation is not full source closure. The required
canonical forcing is (0,1/(CH)). The uniform partition has a generically
nonzero V component. At the actual physical point Z=h=u=v=1,

    kappa=64/729,
    J(dlog(kappa),dlog(H))=59/4,

so the displayed V coefficient is nonzero. Its W coefficient also is not
the required 1/(CH)=1/9. The physical coefficient mismatch remains to be
corrected; it is not removed by the normalizer identity or the partition.

`projector_two_parameter_current.py` verifies the finite normalizer, full
normalized current coefficients, all mixed curvature terms, the partition,
the physical residue and source Jacobian, and the actual nonzero V
residual. The output is `projector-two-parameter-current-results.json`.
