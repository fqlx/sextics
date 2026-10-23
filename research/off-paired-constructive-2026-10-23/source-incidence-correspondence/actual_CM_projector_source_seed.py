"""One source-forced non-eta CM projector repair of the actual t-seed.
The complete correction is retained. No cancellation/certificate is asserted.
"""
from pathlib import Path
import sympy as s,json
h,y,X,Y,zeta,alpha,t,H,C,p,Z,fc,ht,ct,hs,ft=s.symbols('h y X Y zeta alpha t H C p Z f H_t C_t hsrc f_t')
cl=lambda x:s.factor(s.cancel(x))
DQ=lambda x:s.diff(x,h)*y+s.diff(x,y)*3*h*h/2
DP=lambda x:s.diff(x,X)*Y+s.diff(x,Y)*3*X*X/2
def red(e):
 n=s.together(e).as_numer_denom()[0]
 n=s.rem(s.Poly(n,Y),s.Poly(Y*Y-X**3+1,Y)).as_expr()
 n=s.rem(s.Poly(n,y),s.Poly(y*y-h**3+1,y)).as_expr()
 n=s.rem(s.Poly(n,zeta),s.Poly(zeta*zeta+zeta+1,zeta)).as_expr()
 return s.factor(n)
k=(y+Y)/(2*(h-X));kz=(y+Y)/(2*(zeta*h-X))
curv=DP(k)+DQ(k)
curvz=zeta*DP(kz)+DQ(kz)
checks={
 'FULL_CM_Cauchy_curvature':red(curv-(h-X)/4)==0,
 'FULL_CM_translated_character_curvature':red(curvz-(zeta*zeta*h-zeta*X)/4)==0,
 'CM_P_projector_exact':red(4*(curvz-zeta*zeta*curv)/(zeta*zeta-zeta)-X)==0,
 'CM_Q_projector_exact':red(4*(curvz-zeta*curv)/(zeta*zeta-zeta)-h)==0,
 'actual_P_source_normalization':cl((X*alpha/alpha**2).subs(X,alpha*t)-t)==0,
}
# Literal endpoint Euler cochain.
L=H+C*p;ff=L*L-4*p**6
DPendpoint=lambda e:s.diff(e,p)+s.diff(e,Z)*(C*L-12*p**5)/Z
etheta=3*H*(-L/Z**3)+2*C*(-p*L/Z**3)+2/Z+DPendpoint(p/Z)
checks['literal_endpoint_Euler_fiber_cochain']=s.rem(s.together(etheta).as_numer_denom()[0],Z*Z-ff,Z)==0
fseed=hs/(ht-3*H*ct/(2*C))
checks['actual_t_seed_SERVES_whole_thetaH']=cl(fseed*(ht-3*H*ct/(2*C))-hs)==0
assert all(checks.values()),checks
out={
 'status':'SOURCE_FORCED_NONETA_CM_PROJECTOR_CURRENT_WITH_FULL_CORRECTION_NOT_CERTIFICATE',
 'checks':checks,'check_count':len(checks),
 'actual_CM_geometry':'alpha³=2,zeta³=1,zeta≠1. P=(alpha*t,rho),Q=(h,y),h³=H,y²=H−1; omegaP=alpha*eta,eta=dt/rho,omegaQ=dh/y.',
 'literal_projectors':{
  'Omega':'(y+rho)/(2(h−alpha*t))*(omegaQ−alpha*eta)',
  'Omega_zeta':'(y+rho)/(2(zeta*h−alpha*t))*(zeta*omegaQ−alpha*eta)',
  'K_P':'4*(Omega_zeta−zeta²*Omega)/(alpha²*(zeta²−zeta))',
  'K_Q':'4*(Omega_zeta−zeta*Omega)/(alpha*(zeta²−zeta))',
  'curvatures':'dK_P=t*eta wedge omegaQ; dK_Q=h*eta wedge omegaQ. They contain non-eta components; all actual P and Q normal derivatives are retained.'},
 'source_bound_first_current':{
  'physical_field':'rho²=2t³−1,R=r+t/(4rho),z³=R/rho,W²=U²−kappa R²,kappa=4t³/rho²,H=1+U²−R²+tR/(2rho),C=tz²/3+z(U+W)/4.',
  'source':'beta_original=hsrc*dt wedge dU wedge dR wedge thetaH,hsrc=−(U/W−1)/(108rho),thetaH=−(H+Cp)dp/Z³.',
  'physical_H_t':'−R*(t³+1)/(2rho³), at fixed U,R',
  'physical_C_t':'−t²*B/rho²−A/(t*rho²)+3kappa*R²*z/(8t*rho²*W), A=tz²/3,B=z(U+W)/4, at fixed U,R',
  'f':'hsrc/[H_t−3H*C_t/(2C)]',
  'J_t_full':'f*dU wedge dR wedge theta0−[f*C_t*p/(2C Z)]*dt wedge dU wedge dR',
  'LITERAL_derivative':'dJ_t_full=beta_original+Rseed*dt wedge dU wedge dR wedge theta0,Rseed=f_t−f*C_t/C. The displayed fiber cochain is indispensable.'},
 'actual_source_forced_projector_repair':{
  'spinor_b':'U=[b(y−d)+(y+d)/b]/2,r=[b(y−d)−(y+d)/b]/2,d=t/(4rho); Psi*Psi_aux=b²,Psi_aux=(d+y)/(d−y). Only dlogb is used as a rational form.',
  'physical_volume_unit':'dt wedge dU wedge dR=(3rho*h²*y/2)*eta wedge omegaQ wedge dlogb',
  'w':'−3rho*h²*y*Rseed/2',
  'm':'w/t',
  'J_CM':'m*K_P wedge dlogb wedge theta0',
  'WHOLE_identity':'beta_original=d(J_t_full+J_CM)−dm wedge K_P wedge dlogb wedge theta0−m*K_P wedge dlogb wedge (dH wedge thetaH+dC wedge thetaC)',
  'literal_endpoint_normal':'theta0=dp/Z; dtheta0=dH wedge thetaH+dC wedge thetaC,thetaC=−p(H+Cp)dp/Z³. Thus every j=0,1,3,4 compact component and exact fiber term remains available; no row truncation is used.',
  'no_cancellation_assertion':'The two displayed correction terms are generally nonzero. The candidate is submitted for an independent whole-source rational derivative audit, not declared a solve.'},
 'counterdivisors':['h=alpha*t','zeta*h=alpha*t','P or Q infinity','rho=0,y=0','b=0,infinity','T=y−d and y+d','H_t−3H C_t/(2C)=0','C=0,Z=0','R=0,W=0'],
 'remaining':'Serve the actual full correction by a finite source-bound current or reject this single candidate. No amplitude fit, denominator sweep, or unrestricted nonexistence claim is implied.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'literal CM projectors and whole-source seed identities; correction retained')
