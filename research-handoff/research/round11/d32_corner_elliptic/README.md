# D32 corner elliptic surface and actual vertex: handoff

Research stopped at the user's request. This folder contains verified local models, not a certificate and not a global resolved-H20 calculation. The D32 input is the cyclic-triple-residual instance, not the earlier off-paired instance.

## Reproduction and provenance

Run `python model.py`, followed by Singular on `check_order4.sing` and `check_order12.sing`. The latter cover both irreducible factors of zeta^6+1; their logs record exact characteristic-zero squarefreeness, coprimality, and degrees. The model reads the previously extracted coefficients in `/workspace/research/round10/horizontal5/fresh/boundary/blowup_quadratic.json`.

Run `python vertex_newton.py` for the Newton face of the actual 558-term degree-32 D from `/workspace/research/round9/abel_prym/effective_graph.pickle`. It expands the actual Y0 sixth-root series and reduces exactly modulo zeta^6+1. `vertex_newton.json` records the truncation sufficiency bound.

The authoritative physical equation and source are `/workspace/sextics/data/cyclic-triple-residual/instance.rec`, with source A=X0^3 Y0^3.

## Generic exceptional elliptic surface

On Y2=1 set X0=eps, X1=v*eps, X2=W, Y1=b, Y0=a, and a^6+1=b*r. At a=zeta, zeta^6=-1, the transverse weighted initial CI has weights (eps,W,b,r)=(3,2,6,6), degrees (12,12). Its coarse elliptic curve is the intersection of quadrics in (U,b,r,T), where U=W^3 and T=eps^2:

    U^2+b(r+lambda*T)=0,
    A*r^2+C*b*r+D*b^2+T(B*r+E*b)=0,
    lambda=5*zeta/7.

It has the rational point (U,b,r,T)=(0,0,0,1). On b=1 eliminate r=-U^2-lambda*T. With q2=lambda*(B-A*lambda), L1=(2A*lambda-B)*U^2+E-C*lambda, and Y=2*q2*T-L1, the exact quartic is

    Y^2=B^2*U^4+H*U^2+J.

The exact birational map and relative differential are

    x=2B(Y+B*U^2)+H, y=2B*x*U,
    y^2=x^3-2H*x^2+(H^2-4B^2J)*x,
    dx/y=dU/Y.

Write G=(v^6+1)(196v^6+171). The verified factors are B=-926100*zeta^2*G, H=(10/63)*zeta*B^2*(1+zeta*v), J=B*Q14, and H^2-4B^2J=8*lambda*B^3*P14. The two degree-14 polynomials P14,Q14 are squarefree and pairwise coprime, and each is coprime to G over both zeta fields.

These factors and the exact degrees give the minimal elliptic surface: twelve III* fibers at G, fourteen I2 at P14, fourteen I1 at Q14, and I0* at infinity. Thus chi=13, q=0, p_g=12. Its two-form basis is v^j*dv wedge dx/y, 0<=j<=11. This is a statement about this coarse generic exceptional surface.

The physical mu3 action W->omega*W is trivial on its coarse U=W^3 model. Global Y sign acts as elliptic inversion, so all twelve forms have mu3 character zero and Y sign minus. The actual source needs a different character: source H31 has mu3 character one and Y sign plus, hence its H2(O) dual has mu3 character two. Conormal layers, not these twelve coarse forms alone, are essential. The first allowed normal-layer indices are m=1 mod 6 (the local adjoint slots give m=1 and m=7).

## Actual infinity vertex is a different model

The generic exceptional elliptic compactification does not determine the actual conductor family's infinity conditions. Higher terms become dominant. The exact Newton substitution is

    X0=k^6*gamma^3*E, X1=gamma^3*E,
    X2=k^5*gamma^2*W0, Y1=k^18*gamma^6*B,
    a^6+1=k^30*gamma^12*B*R.

There is exactly one positive lower face, from (k,gamma) exponents (60,81) to (90,75), with normal (1,5). Its polynomial is recorded in `vertex_newton.json`. Consequently the crossover is gamma=k^5*eta. In physical coordinates its primitive weights are

    (X0,X1,X2,Y1,delta)=(7,5,5,16,30), delta=a^6+1.

The initial physical F has degree 30 and eliminates delta. The initial D is 57624*zeta*X1^12*P95, where

    P95=1000*zeta^3*X0^6*X1*Y1^3
       +3150*zeta^2*X0^4*X1*Y1^2*delta
       -9261*X1^7*delta^2-3150*zeta*X0^7*Y1*delta
       -6615*X0^5*delta^2.

Its new main coarse component is rational, not the p_g=12 surface. A direct function-field parametrization uses

    v=X2/X1, z=X0^2*Y1/X1^6, h=X0^5/X1^7,
    d=delta/X1^6=-(1+v^6)-lambda*z,
    h=(-9261*d^2+3150*zeta^2*z^2*d+1000*zeta^3*z^3)
      /(6615*d^2+3150*zeta*z*d).

These invariants generate the full degree-zero field: the exponent lattice is saturated. One inverse weighted parametrization is [X0:X1:X2:Y1]=[h^3:h^2:v*h^2:z*h^6]. Fresh independently checked this parametrization. The nonreduced X1^12 component is a rational weighted plane. Their reduced intersection curves are rational as well; multiplicity and conormal corrections remain uncomputed.

At the generic point of the new main component, D has valuation155 and the smooth ambient weighted blowup has discrepancy32 (weights sum33). Thus a physical canonical numerator P must have weight at least123 there. This necessary valuation was independently agreed with Fresh. P must be evaluated on the physical sextic, retaining delta Taylor cancellations. Bounds obtained for four explicit generic adjoint families are not bounds on the full global image, because other global polynomials can cancel weighted initial faces.

## Remaining obligations

The actual infinity normalization, nonreduced component, further valuations, conormal layers, and global adjoint connecting map must be calculated before making any global H20 claim. Even a surviving global H20 class must be paired with the actual A deformation and its correct stabilizer character. No such source-serving calculation or certificate is completed here. Fresh owns further actual vertex normalization; certificate_search owns global adjoint interpolation and finite v^6+1 corners; rank_candidates owns the 196v^6+171 and Y2=0 collisions.

For the separate Chebyshev route, the complete handoff is `/workspace/research/round9/chebyshev/README.md`. It includes the corrected actual trace-dual weights and explicitly withdraws the apparent one-dimensional RES interpolation shortage.
