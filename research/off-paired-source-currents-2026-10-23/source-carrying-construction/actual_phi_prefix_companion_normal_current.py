"""ONE combined actual phi_H prefix and companion-normal source current.
Retains the full physical inverse Jacobian in the explicit prefix/cochain;
its complete remaining correction has no E denominator. Not a certificate.
"""
from pathlib import Path
import json,sympy as s
x,y,z,p,Y=s.symbols('x y z p Y',nonzero=True)
H=1+x**6+y**6+z**6+x*y*z/2
C=x**3*z/2+x*y/3;A=y**3;qmark=-3*z/2
J=s.expand(H+qmark*C)
w=y*y/x;q=x*y;u=x**3
eta=2*u+w**3-3*z*z/4
T=s.factor(s.diff(J,y)*s.diff(C,x)-s.diff(J,x)*s.diff(C,y))
Phi=-A/(6*T)
CJ=(z/2+w/(6*q))/eta
F=s.factor(Phi*CJ)
Nx=-x/(3*T);Ny=s.diff(C,x)/T
N=lambda f:Nx*s.diff(f,x)+Ny*s.diff(f,y)
PhiH=N(Phi)
# The old whole prefix Jphi=Phi*dC wedge dz wedge theta.
vpx=s.factor(Phi*s.diff(C,y));vpy=s.factor(-Phi*s.diff(C,x))
# Retained cochain F*dJ wedge dz wedge theta.
vcx=s.factor(F*s.diff(J,y));vcy=s.factor(-F*s.diff(J,x))
# Their actual combined current is the simple source companion normal.
vx=s.factor(A/(18*x*x*eta));vy=s.factor(y**4/(36*x**3*eta))
Div=s.factor(s.diff(vx,x)+s.diff(vy,y))
L=H+C*p;curve=L*L-4*p**6
checks={}
def ck(n,e):
    v=s.factor(e);checks[n]=v==0
    assert v==0,(n,v)
ck('actual_fixed_C_normal_H',N(H)-1)
ck('actual_fixed_C_normal_C',N(C))
ck('actual_fixed_C_normal_J',N(J)-1)
ck('maintained_phi_prefix_x',vpx-vcx-vx)
ck('maintained_phi_prefix_y',vpy-vcy-vy)
ck('WHOLE_companion_normal_divergence',Div+A/(3*eta**2))
vH=vx*s.diff(H,x)+vy*s.diff(H,y)
vC=vx*s.diff(C,x)+vy*s.diff(C,y)
ck('WHOLE_companion_endpoint_C_motion',vC-A*CJ/6)
ck('WHOLE_companion_endpoint_H_motion',vH-A*(1-qmark*CJ)/6)
# Literal full physical four-form derivative, including EVERY theta derivative.
beta=-A*L/(6*Y**3)
dJ1=Div/Y-L*(vH+p*vC)/Y**3
remainder=A/(3*eta**2*Y)+A*CJ*L*(p-qmark)/(6*Y**3)
ck('ENTIRE_original_source_minus_combined_current',beta-dJ1-remainder)
# Old phi_H correction transported to the new companion and its exact cochain.
# Differentiate old current directly rather than using a relative-only claim.
DivPrefix=s.diff(vpx,x)+s.diff(vpy,y)
ck('WHOLE_old_phiH_correction',DivPrefix+T*PhiH)
# Source companion coefficient rho=w/(36eta). For relative fixed(J,z),
# u_J=1/eta, q_J=w/(2qeta), so C_J=CJ is literal.
U,W,Q,JJ,ZZ=s.symbols('u w q J z',nonzero=True)
alpha=3*ZZ*ZZ/4;etaB=2*U+W**3-alpha
E=etaB-3*W**3-9*ZZ*Q*W*W
Cw=U*E/(6*Q*etaB)
PhiNew=Q*W/(6*U*E);CJnew=(3*ZZ*Q+W)/(6*Q*etaB)
rho=W/(36*etaB)
Gb=s.groebner([Q*Q-U*W,U*U+(W**3-alpha)*U+1+ZZ**6-JJ],Q,U,domain=s.QQ.frac_field(W,JJ,ZZ))
def red(e):return s.factor(Gb.reduce(s.cancel(e).as_numer_denom()[0])[1])
def ckr(n,e):
    a=red(e);checks[n]=a==0
    assert a==0,(n,a)
ckr('ENTIRE_phi_jacobian_source_unit',PhiNew*Cw-rho)
# Fixed C normal and relative source-coordinate derivative are different.
NU=1/E;NW=-(W+3*ZZ*Q)/(U*E);NQ=-3*ZZ/(2*E)
NN=lambda e:s.diff(e,JJ)+NU*s.diff(e,U)+NW*s.diff(e,W)+NQ*s.diff(e,Q)
DW=lambda e:s.diff(e,W)-3*U*W*W/etaB*s.diff(e,U)+(U-3*U*W**3/etaB)/(2*Q)*s.diff(e,Q)
rhoJ=-W/(18*etaB**3)
ckr('FULL_relative_Piola_normal_with_cochain',NN(PhiNew)*Cw-rhoJ+DW(PhiNew*CJnew))
# Whole E-free packet in the new source coordinates; no endpoint row frozen.
packet_even0=W/(18*etaB**3)
packet_evenC=ZZ*W/(72*etaB**2)
packet_odd=W*W/(216*Q*etaB**2)
ckr('ENTIRE_packet_endpoint_tau_unit',rho*CJnew-packet_evenC-packet_odd)
# Independent normalization of BOTH whole residual rows onto the actual
# genus4 CM kernel; no term or source character is projected away.
ll,UU,WW,QQ=s.symbols('lambda U W Q',nonzero=True)
Delta=UU-1/UU
Araw=6*ll**6*QQ*Delta**2/WW**2*(-WW/(18*ll**8*Delta**3))
Braw=6*ll**6*QQ*Delta**2/WW**2*(z*WW/(72*ll**5*Delta**2)+WW**2/(216*ll**6*QQ*Delta**2))
for name,expr in [('FULL_normalized_theta_row',Araw+UU/(3*ll**2*QQ*Delta)),('FULL_normalized_tau_row',Braw-(1+3*ll*z*UU/QQ)/36)]:
    num=s.cancel(expr).as_numer_denom()[0]
    checks[name]=s.factor(s.rem(num,QQ*QQ-UU*WW,QQ))==0
    assert checks[name]
# Exact point checks use the ORIGINAL physical chart.

pt={x:1,y:1,z:1,p:1}
ev=lambda f:s.factor(f.subs(pt))
rv=s.factor(s.cancel(remainder*Y**3).subs(Y**2,curve).subs(pt))
assert rv!=0
out={
 'status':'PASS_ONE_COMBINED_PHI_PREFIX_AND_COMPANION_NORMAL_CURRENT_WITH_ENTIRE_REMAINDER; NOT_CERTIFICATE',
 'physical_source':'beta=−y^3(H+Cp)dxdy dz dp/(6Y^3), Y^2=(H+Cp)^2−4p^6; H=1+x6+y6+z6+xyz/2,C=x3z/2+xy/3.',
 'OLD_complete_prefix':'Phi=−y^3/(6T), T=J_y C_x−J_x C_y, J=H−3zC/2. Jphi=Phi*dC wedge dz wedge dp/Y; beta−dJphi=−Phi_H*dH wedge dC wedge dz wedge dp/Y with Phi_H=partial_H|C,z(Phi).',
 'NEW_source_normal_cochain':'CJ=(z/2+w/(6q))/etaB, F=Phi*CJ, w=y²/x,q=xy,etaB=2x³+y6/x³−3z²/4. Subtract the ENTIRE rational cochain F*dJ wedge dz wedge dp/Y; its Phi/T/E/q source factors and derivatives are retained.',
 'ONE_actual_combined_current':'J1=Jphi−F*dJ wedge dz wedge dp/Y=w/(36etaB)*dw wedge dz wedge dp/Y. In original coordinates i_v(dxdy dz) wedge dp/Y with vx=y³/(18x²etaB),vy=y4/(36x³etaB),vz=0.',
 'WHOLE_source_identity':'beta=dJ1+R, R=dJ wedge dw wedge dz wedge dp*[w/(18etaB³Y)+(z*w/(72etaB²)+w²/(216q etaB²))*(H+Cp)*(p+3z/2)/Y³]. BOTH Y^-1 and Y^-3 terms are compulsory.',
 'physical_equivalent_remainder':'R=dxdy dzdp*[y³/(3etaB²Y)+y³*CJ*(H+Cp)*(p+3z/2)/(6Y³)].',
 'source_branch_scope':'T/E poles are in the retained actual cochain F, not thrown away. R retains etaB=0, q=0 and every endpoint and moving-source character. No normalized unweighted projection is used.',
 'FULL_relative_phiH_reduction':'Phi_H*dC=−w dw/(18etaB³)−d_w(Phi*CJ) at fixed(J,z). Full endpoint integration adds the explicit CJ*(partial_C+3z*partial_H/2)(dp/Y) term in R.',
 'ENTIRE_normalized_CM_kernel_packet':'R=dλ wedge Ωodd wedge dz wedge [−U/(3λ²QΔ)*theta+(1+3λ*z*U/Q)/36*tau(theta)], Δ=U−1/U,tau=partial_C+3z*partial_H/2, Ωodd=−dlogU/(3QΔ), λ6=1+z6−J. BOTH theta and tau(theta) rows are required.',
 'new_four_channel_binding':'Even packet uses 2 varying elliptic quotients of q-even genus2; odd packet uses BOTH actual CM quartic quotients of the genus4 q-cover. Neither compact channel nor finite pole charge is discarded.',
 'actual_point':{'x':'1','y':'1','z':'1','p':'1','etaB':str(ev(eta)),'CJ':str(ev(CJ)),'Divv':str(ev(Div)),'Y_squared':str(ev(curve)),'ENTIRE_remainder_times_Y_cubed':str(rv)},
 'checks':checks,'check_count':len(checks),
 'open':'Construct a finite actual correction for the ENTIRE displayed two-term packet, keeping full endpoint C coupling, all four elliptic channels, moving scales/moduli, finite charges and infinity corrections. No closure or certificate.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'ENTIRE combined physical current/source/normal/cochain; remaining numerator at point',rv)
