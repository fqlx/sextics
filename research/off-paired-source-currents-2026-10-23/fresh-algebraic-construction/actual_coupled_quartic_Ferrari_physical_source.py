"""One exact coupled quartic/Ferrari correspondence for the WHOLE source.

No unweighted all-root trace is treated as a primitive.  The actual two-root
source, its nonconstant normal, its complement character and finite recovery
of an original marked root are explicit.  Primitive construction remains open.
"""
from pathlib import Path
import json
import sympy as s

ell,g,v,xi,E,F,x,b,z,e,f=s.symbols('ell g v xi E F x b z e f',nonzero=True)
H,L,D,c,ze,ss=s.symbols('H L D c zeta s',nonzero=True)
eps=s.symbols('eps')
checks={}
def ck(name,expr,rels=()):
    num=s.together(expr).as_numer_denom()[0]
    for gen,poly in rels:
        num=s.rem(num,poly,gen)
    red=s.factor(num)
    checks[name]=red==0
    assert checks[name],(name,red)

# Original Y0=1 source chart and literal normal.  Coordinates are ordered
# (x,b,z,e,f), so the original projective Omega5 has positive sign.
Forig=x**6+b**6+1+z**6+e**6+f**6+x**3*b*z/2+b**3*z*e*f/2+x*x*b*e*f/3
sub={x:ell*xi,b:ell**2,z:ell*v,e:ell*E,f:ell*F}
Lphys=v*E*F/2
Hphys=xi**6+v**6+E**6+F**6+v*xi**3/2+xi*xi*E*F/3
P=g**4+L*g**3+H*g*g+D*g+1
ck('IMMUTABLE_entire_quartic_pullback',
   Forig.subs(sub,simultaneous=True)-P.subs({g:ell**3,H:Hphys,L:Lphys,D:0}))
jac=s.det(s.Matrix([[s.diff(q,w)for w in [ell,v,xi,E,F]]for q in [ell*xi,ell**2,ell*v,ell*E,ell*F]]))
ck('FULL_original_source_Jacobian',jac-2*ell**5)
ck('FULL_original_source_g_Jacobian',jac/(3*ell*ell)-2*ell**3/3)
ck('FULL_original_A_source_density',ell**3*xi**3*jac/(3*ell*ell)-s.Rational(2,3)*xi**3*ell**6)
ck('WHOLE_physical_epsilon_normal',
   (Forig-eps*x**3).subs(sub,simultaneous=True)
   -P.subs({g:ell**3,H:Hphys,L:Lphys,D:-eps*xi**3}))

# Ferrari incidence, without choosing or freezing a resolvent root.
alpha=(L*c*c-D*c)/(c*c-1)
beta=(D*c-L)/(c*c-1)
zc=c+1/c
R=(ze-H)*(ze*ze-4)-L*L-D*D+L*D*ze
Rc=R.subs(ze,zc)
q=g*g+alpha*g+c
qb=g*g+beta*g+1/c
ck('FERRARI_L_coefficient',alpha+beta-L)
ck('FERRARI_D_coefficient',alpha/c+beta*c-D)
ck('FERRARI_H_incidence',zc+alpha*beta-H-Rc/(zc*zc-4))
ck('WHOLE_quartic_factor_WITH_incidence_defect',q*qb-P-g*g*Rc/(zc*zc-4))
ck('FERRARI_complement_swaps_alpha',alpha.subs(c,1/c)-beta)
ck('FERRARI_complement_swaps_beta',beta.subs(c,1/c)-alpha)

# Physical normal acts on the chosen Ferrari sheet.  Its D-normal cannot
# be frozen, and is stated before setting the physical coefficient D=0.
Rz=s.diff(R,ze)
Rzz=s.diff(Rz,ze)
zD=(2*D-L*ze)/Rz
ck('WHOLE_resolvent_normal',s.diff(R,D)+Rz*zD)
cD=c*c*zD.subs(ze,zc)/(c*c-1)
ck('WHOLE_conic_normal',(1-1/c**2)*cD-zD.subs(ze,zc))
ck('WHOLE_physical_epsilon_resolvent_normal',
   (-xi**3*zD).subs(D,0)-xi**3*L*ze/Rz.subs(D,0))

# Exact source on an original marked root, from the actual double pole.
Pg=s.diff(P,g)
Pgg=s.diff(Pg,g)
gD=-g/Pg
source_root=s.Rational(2,3)*xi**3*(2*g*Pg-g*g*Pgg)/Pg**3
DD_volume=s.diff(g/Pg,D)+s.diff(g/Pg,g)*gD
ck('WHOLE_marked_root_source_residue',source_root+s.Rational(2,3)*xi**3*DD_volume)

# Literal two-root trace by an inverse modulo the selected quadratic.
# For q=g²+ag+c, qbar modulo q is u*g+w.  The coefficient of g
# in rem[g/qbar,q] is sum g/(q' qbar), with all source weights retained.
aa,bb=s.symbols('alpha beta')
uu=bb-aa
ww=1/c-c
N=ww*ww-aa*uu*ww+c*uu*uu
inv=(ww-aa*uu-uu*g)/N
ck('EXACT_selected_quadratic_Bezout_inverse',
   s.rem(s.together(((uu*g+ww)*inv-1)*N),g*g+aa*g+c,g))
g_rem=(ww*g+c*uu)/N
ck('EXACT_selected_pair_g_weight',
   s.rem(s.together((g*inv-g_rem)*N),g*g+aa*g+c,g))
Nactual=N.subs({aa:alpha,bb:beta})
ck('EXACT_resultant_equals_resolvent_derivative',
   Nactual-Rz.subs(ze,zc)+2*zc*Rc/(zc*zc-4))
# On R=0, sum_{qroots} g/Pg=(c^-1-c)/Rz=-s/Rz.
ck('EXACT_complement_odd_pair_unit',
   ((1/c-c)/Rz.subs(ze,zc)).subs(c,1/c)+(1/c-c)/Rz.subs(ze,zc))

# The ACTUAL source is its full physical D derivative.  Keep the
# complement-odd square root s²=zeta²-4, not a constant pair trace.
sD=ze*zD/ss
pair_source=s.Rational(2,3)*xi**3*(sD/Rz-ss*(s.diff(Rz,D)+Rzz*zD)/Rz**2)
pair_source0=pair_source.subs(D,0)
compact0=4*xi**3*L*(H*ze**3-2*ze**2-8)/(3*ss*Rz.subs(D,0)**3)
ck('WHOLE_actual_source_pair_at_physical_D0',pair_source0-compact0,[(ss,ss*ss-ze*ze+4)])
ck('WHOLE_actual_source_pair_complement_odd',compact0.subs(ss,-ss)+compact0)

# One finite source-specific normal transfer, with its moving coefficient.
# This is a literal identity, not an assertion that physical L-integration
# terminates.  It retains the derivative of zeta multiplying the primitive.
Rz0=Rz.subs(D,0)
zL=2*L/Rz0
sL=ze*zL/ss
DL_zs_over_R=(zL*ss+ze*sL)/Rz0-ze*ss*Rzz*zL/Rz0**2
ck('WHOLE_D_normal_to_L_normal_identity',
   pair_source0+s.Rational(1,3)*xi**3*DL_zs_over_R,
   [(ss,ss*ss-ze*ze+4)])

# Source-preserving finite recovery, rather than asserting tracezero solves.
B1,B2,B3,B4=s.symbols('beta1 beta2 beta3 beta4')
ck('FINITE_three_pairs_recover_original_source',
   ((B1+B2)+(B1+B3)+(B1+B4))/2-B1-(B1+B2+B3+B4)/2)

out={
 'status':'ACTUAL_COUPLED_QUARTIC_FERRARI_SOURCE_CORRESPONDENCE_WITH_NONZERO_COMPLEMENT_ODD_UNIT; NOT_PRIMITIVE',
 'original_chart':'Y0=1,(x,b,z,e,f)=(X0,X1,Y1,X2,Y2),Omega5=+dx db dz de df,A=x^3.',
 'actual_finite_coordinate_map':'Choose ell^2=b, g=ell^3=b^(3/2), and x=ell*xi,z=ell*v,e=ell*E,f=ell*F. Then F=P=g^4+L g^3+H g^2+1, L=vEF/2,H=xi^6+v^6+E^6+F^6+v xi^3/2+xi^2 EF/3. The coordinate Jacobian for (g,v,xi,E,F) is exactly +2g/3.',
 'WHOLE_physical_source':'A Omega5/F^2=(2/3)xi^3 g^2 dg wedge dv wedge dxi wedge dE wedge dF/P^2. Physical F-eps*A is P_D with D=-eps*xi^3. This is the immutable source and actual physical normal, not an arbitrary polynomial g numerator.',
 'Ferrari_incidence':'R=(zeta-H)(zeta^2-4)-L^2-D^2+LD zeta=0; choose c+c^-1=zeta, s=c-c^-1. alpha=(Lc^2-Dc)/(c^2-1),beta=(Dc-L)/(c^2-1). Then P=(g^2+alpha g+c)(g^2+beta g+c^-1). The exact off-incidence discrepancy is g^2*R/(zeta^2-4); the c-sheet exchanges the two complementary pairs.',
 'WHOLE_moving_normal':'zeta_D=(2D-L zeta)/Rz, c_D=c^2 zeta_D/(c^2-1), alpha_D and beta_D are TOTAL derivatives through this c_D. At D=0 the physical epsilon normal is zeta_eps=xi^3 L zeta/Rz. L,H and xi,v,E,F are fixed only under this actual epsilon normal; their ordinary base variations are not discarded.',
 'WHOLE_marked_root_density':'For a selected original root g, the actual q1 residue density is (2xi^3/3)[2g Pg-g^2 Pgg]/Pg^3 *dv dxi dE dF = -(2xi^3/3)D_D[g/Pg] dbase4, with g_D=-g/Pg.',
 'EXACT_selected_pair_trace':'For the chosen quadratic q, its norm against qbar is Res(q,qbar)=Rz on R=0. Exact quadratic Bezout gives sum_{q roots}g/Pg=(c^-1-c)/Rz=-s/Rz. The complementary pair has the opposite unit. The g weight is essential.',
 'WHOLE_actual_source_pair':'The selected-pair WHOLE physical source is (2xi^3/3)D_D[s/Rz] dbase4. At the physical D=0 it equals 4xi^3 L(H zeta^3-2zeta^2-8)/(3s Rz^3) dv wedge dxi wedge dE wedge dF. Both the resolvent normal and the conic normal are included. This is a nonconstant complement-odd source; no unweighted all-pair trace is substituted.',
 'EXACT_source_normal_transfer':'At D=0, D_D(s/Rz)=-(1/2)D_L[zeta*s/Rz], where both are TOTAL derivatives on R0=0 and s^2=zeta^2-4, with H fixed. Hence the actual pair source is -(xi^3/3)D_L[zeta*s/Rz] dbase4. The derivative of the nonconstant zeta coefficient is retained. Physical L=vEF/2 and H_v=6v^5+xi^3/2; using this transfer still requires a genuine physical-base primitive, not a formal coefficient integration.',
 'FINITE_source_recovery':'Let beta_i be the original marked-root sources, sum_i beta_i=0 (the exact total trace, not a primitive). The three selected pairs containing i satisfy sum_{j!=i}(beta_i+beta_j)=2beta_i. Thus a primitive for the displayed actual pair source, compatibly on its finite cover, would return the original by the finite three-pair correspondence and factor1/2. The pair source itself still has to be served.',
 'scope':'This verifies the proposed new coupled quartic/conic/cubic equation and its actual weighted source. It does not infer exactness from Ferrari factorization, polynomial degree, zero total trace, generic Fano geometry, or a denominator window.',
 'checks':checks,'check_count':len(checks)
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual coupled quartic/Ferrari physical source and complement-odd selected-pair unit')
