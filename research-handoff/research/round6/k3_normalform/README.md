Exact Jacobian normal form for the source-bound quartic-cover K3 family
--------------------------------------------------------------------

For the plane cubic

 C=A U^3-h V^3-s Z^3+d U^2 V+g U V Z+f U Z^2,

the Fisher-normalized Jacobian is y^2=x^3+I4(s)x+I6(s), with

 I4=(9/2)Agh*s-hdf^2-g^4/48,
 I6=(-27A^2h^2/4+hd^3)s^2+(hd^2fg+5Ahg^3/8)s-Ah^2f^3+hdf^2g^2/12+g^6/864.

`hessian_check.py` verifies the FULL exact polynomial identities by the independent Hessian-of-Hessian relation

 Hess(Hess C)=110592 I4^2 C-13824 I6 Hess C,

calibrated on y^2z-x^3-I4xz^2-I6z^3. Every coefficient agrees. No numerical interpolation or unverified invariant formula is used for this identity.

The physical lambda0 specialization is A=1+q^6,d=q/2,g=1/3,f=q^2/[4(h^2-4)]. A constant-x anti-invariant section after s=t+t^-1 must have x0=-(5Ag^2+8d^2f)/(36A) and satisfy x0^3+a0*x0+b0+4b2=0. `test_constant_section.py` computes this obstruction exactly. It is nonzero at q=1,h=3, namely -52814298486089/54419558400, hence that proposed section does not exist generically.

Primary literature reviewed: Abhinav Kumar, "Elliptic fibrations on a generic Jacobian Kummer surface", arXiv1105.1715v3, Theorem2 and tablep9. Its25 elliptic-fibration types on the Picard17 Jacobian Kummer lattice include no configuration containing twoE6 fibers. Thus the natural twoIV* fibration does not by itself identify this family with an ordinary Picard17 principally polarized Jacobian Kummer surface. https://arxiv.org/pdf/1105.1715

Subsequently reflection_skew and cycle_geometry independently found and audited a good lambda0 rank16 reduction. Root halted the extra-NS/Kummer search. The displayed Jacobian identities remain valid and useful; no extra section, extra NS class, Kummer identification, source primitive or certificate is asserted here.

First lambda jets and the constructive rank-two connection
---------------------------------------------------------

The new task continues with the valid elliptic K3 model independently of extra NS. For C_e=C+e*U^2*Z, the exact first coefficient jets at e=0 are

 I4_e=-h*(6*d*k-f*g)/2,
 I6_e=-h*(108*A*f*h*k+18*d*g^2*k+f*g^3)/24.

`lambda_gm.py` derives these by differentiating the entire Hessian-of-Hessian identity and checks every polynomial coefficient exactly. The physical e_lambda=-q*h/[2(h^2-4)] gives the lambda jets; A_lambda=0 at lambda0.

Let r=h^2-4,J=1+q^6. On the h double cover, scale Weierstrass coordinates by x_new=r*x_old,y_new=r^(3/2)*y_old. The new coefficients are the exact polynomials

 a=(3/2)*J*h*r^2*k-h*q^5/32-r^2/3888,
 b=h*r^3*(q^3/8-27*J^2*h/4)*k^2
   +h*r^2*(q^4/48+5*J*r/216)*k
   -J*h^2*q^6/64+h*q^5*r/3456+r^3/629856.

Their first physical lambda jets are

 a_lambda=q^2*h^2*(36*r*k-q)/48,
 b_lambda=q^2*h^2*r*(108*r*k+2916*J*q*h*k+q)/5184.

All compact expressions are checked against the original rational coefficients before scaling. `lambda_gm.pickle` contains SymPy-exact original/scaled coefficients, jets, discriminants, matrices, source and twisted matrices. The original source comparison and its exact moving-map terms remain audited separately by rank_candidates; this packet does not assert those terms vanish.

For y^2=x^3+a*x+b, use basis omega0=dx/y,omega1=x*dx/y and Delta=4*a^3+27*b^2. With z_D=3*b*D(a)-2*a*D(b) and t_D=2*a^2*D(a)+9*b*D(b), columns of the exact connection are

 G_D=1/(2Delta)*[[-t_D,a*z_D],[3*z_D,t_D]].

`universal_gm.py` solves and checks the exact Hermite identities

 D(omega_n)=sum_i G_D[i,n]*omega_i+d_x(r_n/y).

It exports both rational correction polynomials and proves the universal connection curvature zero exactly. There is no omitted fiber-exact remainder. The convention for coefficient columns is therefore nabla_D H=D(H)+G_D*H.

The root's source column is -G_lambda*(1,0)^T up to its fixed nonzero differential normalization and the retained exact moving-map terms. After the scaling above, the factor sqrt(r) in omega0_old cancels the original1/sqrt(r) density. Thus only k carries the base-density twist: the three divergence operators are partial_k+G_k-k/(k^2-4), partial_q+G_q, partial_h+G_h. This gives a concrete linear rational-current PDE for an actual certificate search; no solution is claimed in this packet.
