# Odd genus2 divisors with a prescribed constant elliptic factor

These are constructive, explicitly source-compatible deck-odd factor families. They are not yet a serving certificate: the intrinsic twist surface irregularity and the actual Gysin class remain to be solved.

On the scaled physical elliptic fourfold W²=k²−4, y²=x³+A(k)x+B(k), take the horizontal moving line x=s k+t. Its odd Prym curve is

    Z²=(k²−4) C(k),
    C(k)=s³k³+c2 k²+c1 k+c0,
    c2=3s²t+a1s+b2,
    c1=3st²+a1t+a0s+b1,
    c0=t³+a0t+b0.

Introduce v and a CONSTANT Legendre parameter ell, with

    r=v+1/v, sigma=4ell/v, pi=4ell+4ell/v²−4.

Require C=s³(k−r)(k²−sigma k+pi). This is the explicit three-equation finite-cover model

    v c2+s³(v²+1+4ell)=0,
    v²c1−s³[(8ell−4)v²+8ell]=0,
    v³c0+4s³(v²+1)[(ell−1)v²+ell]=0.

The involution k→(rk−4)/(k−r) swaps k=±2 and exchanges∞ with r. The exact elliptic quotient is

    X=v(k²−4)/[4(k−r)],
    Y=Z(k−2/v)/(k−r)²,
    Y²=64(s/v)³ X(X−1)(X−ell),
    dX/Y=(v/4)(k−2v) dk/Z.

`legendre_family.py` verifies all rational identities symbolically. The smoothness conditions s*v*(v²−1)*(v²−ell)*ell*(ell−1)≠0 ensure a smooth genus2 curve and a nondegenerate elliptic quotient.

For ell=1/2 this has constant j1728; `model.py` also supplies the centered X³−X form. A good mod107 point at physical(q,h)=(1,4) is(s,t,v)=(36,1,34), with Jacobian determinant63. For ell²−ell+1=0 it has constant j0; mod103,ell57 gives nonsingular points(13,67,18) and(65,82,98), determinants64,27. Multivariate Hensel lifting gives characteristic-zero points and an étale local projection to(q,h), hence a component generically finite dominant over the physical base in BOTH cases. This is an existence proof for actual horizontal divisors, not just a dimension count.

The only residual quadratic twist is alpha=s/v. Over w²=alpha, Y/(8alpha w) lies on the fixed elliptic curve E_ell. A global deck-odd Hol2 on the divisor requires an intrinsic odd Hol1 on this twist-cover base. Artificially adjoining an unrelated positive-genus curve would trace to zero and does not solve this condition. The j1728 finite-field squareclass probe finds both signs of alpha at every tested fixed q, so no simple whole-cover alpha=f(q)*square identity is evident; component-specific possibilities remain open. Agent off_paired is investigating these intrinsic covers.

## Explicit Gysin representative

Suppose beta=w theta is a CLOSED intrinsic odd1-form on the twist cover, theta=theta_q dq+theta_h dh. Its closedness is dtheta+(dalpha/2alpha)∧theta=0. Set

    a(k)=(k−2/v)/(k−r)², L=sk+t,
    H=(k²−4)a(k)²/(64alpha³),
    D_J=det(theta,dJ,dX) in coordinates(q,h,k).

The logarithmic extension d(x−L)/(x−L)∧beta∧dX/Y_fixed has residue beta∧omega_E on the divisor. Differentiating cancels the moving-line pole and gives, up to one orientation sign, the top4-form with numerator

    4alpha²/a(k) * [3(x+L) D_L+D_A+(x²+Lx+L²+A) D_logH]

times dq dh dk dx/(W y³). Poles of the elliptic quotient map and other displayed denominators can remain; they must be tracked as additional support or canceled in any final certificate. This gives a concrete algebraic map from candidate intrinsic1-forms to source representatives. The factor is derived from Y_fixed=W y a(k)/(8alpha w), and its off-divisor elliptic equation differs by H*(x−L)*(x²+Lx+L²+A).

For P=p0+p1x+p2x², relative elliptic reduction is

    [P dx/y³] = c0[dx/y]+c1[x dx/y],
    c0=(2A²p1−3ABp2+9Bp0)/(4A³+27B²),
    c1=(−2A²p2+6Ap0−9Bp1)/(4A³+27B²).

`gysin_probe.py` and `gysin_probe_j0.py` implement this map at good finite-cover points. No k-independent theta matched the actual source representative pointwise in the tested examples. This is only a failure of a strong sufficient representative equality: further exact base currents and traces can change the representative, so it is not an exclusion of either divisor family.
