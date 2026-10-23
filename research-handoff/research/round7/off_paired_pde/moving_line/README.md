# Moving line / isotrivial elliptic seed, with retained physical twist

Universal incidence calculation only; no serving-source claim.

Write the scaled Jacobian equation as y²=x³+(a1*k+a0)x+(b2*k²+b1*k+b0). On x=s*k+t, this becomes y²=c3*k³+c2*k²+c1*k+c0, with c3=s³,c2=3s²t+a1s+b2,c1=3st²+a1t+a0s+b1,c0=t³+a0t+b0.

The j=0 condition c2²-3c3c1=0 is linear in t and gives

 t=[3a0s⁴+3b1s³-(a1s+b2)²]/[3s²(a1s+2b2)].

Then X=s³k+c2/3,Y=s³y satisfy Y²=X³+F6, where F6=s⁶c0-c2³/27. derive.py verifies these universal identities exactly and writes the fully expanded rational F6. Imposing F6=f(q) gives a slope equation of degree8. If f(q) has degree12, e.g.1+q¹², the isotrivial surface Y²=X³+f(q) has the holomorphic2-form dX/Y wedge dq. A degree6 f instead gives a rational elliptic surface and does not supply this holomorphic2-form.

Crucial physical-source limitation: the actual source-bound model also retains W²=k²-4 and density1/W. The moving-line curve together with W is a genus3 V4 cover of the k-line (generically). Its quotients are the elliptic curve E:y²=cubic(k), the rational curve W²=k²-4, and the genus2 curve Z²=(k²-4)*cubic(k), with Z=yW. Thus Jac(D) is isogenous to E times Jac(C_genus2). The physical differential dk/(yW) lies in the genus2 factor. The obvious isotrivial elliptic2-form is even under W negation and does not serve the required odd source. A successful construction must retain and transport the genus2/Prym component; merely imposing j=0 or producing the elliptic companion is insufficient.

## Chebyshev odd elliptic factors

chebyshev.py imposes c2=0,c1=-3c3 by t=-(a1*s+b2)/(3*s²) and9s⁶+3a0s⁴+3b1s³+a1b2s+b2²=0. Then the actual odd genus2 curve is Z²=s³(k²-4)(k³-3k-tau).

Root derived its first degree3 elliptic quotient X=k³-3k,Y=(k²-1)Z, with Y²=s³(X²-4)(X-tau) and dX/Y=3dk/Z. second_elliptic.py independently derives and verifies the other quotient R=(k³-4tau)/(k²-4),Y=(k³-12k+8tau)Z/(k²-4)², with Y²=s³(R³-27R+27tau),dR/Y=kdk/Z. Thus the entire odd hol1 basis is transported exactly. Global Hol2 still requires the slope-twist character and closedness; no Gysin conclusion follows from these fiber identities alone.

## Intrinsic fixed-j0 boundary and actual source jets

The fixed-j0 family is reflection_skew's /round7/moving_j1728/legendre_model.pickle. Its twist is w=s/v. On the boundary v→0, with s=w*v, the nondegenerate b2=0 component has h=q³/[54(1+q⁶)²] and t=-b1/a1. Let J=1+q⁶ and G(q) be the degree24 polynomial in j0_boundary.json. Exact calculation gives

 w³/(h²-4)=[ell*G(q)/(17006112*J⁴)]², ell²-ell+1=0.

Thus the intrinsic quadratic character reduces on this boundary to the physical sqrt(h²-4) character already present. The corresponding reduced curve xi²=11664J⁴-q⁶ is squarefree of degree24, genus11, with hol1 basis q^j dq/xi for0≤j≤10. This produces boundary candidates only; no unrelated auxiliary cover was introduced.

The actual normal lambda jet has b2_lambda=0. j1728_boundary_jet.py and j0_boundary.py compute it exactly and show that the displayed squareclass persists to first order: the derivative is2ell² R0 R0_lambda with R0=G/(17006112J⁴) and rational R0_lambda(q). This does not by itself bind a nonzero source/Gysin image.

For extension into the intrinsic surface, j0_boundary_normal.py differentiates in its normal parameter v. It gives(w³)_v=R1(q)w+R3(q)w³, where R1 is nonzero and divisible byG once. This mixes the boundary mu3 character, while preserving its double-zero conductor atG=0 to first order. Therefore extension of the genus11 hol1 is not automatic. Cycle_geometry is independently auditing normalized generic-cut Kodaira–Spencer/global H10; reflection_skew is handling the actual fixed-j source correspondence. No global odd Hol1, regular odd Hol2, or physical certificate is asserted here.
