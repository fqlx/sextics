"""One actual descended Y+CM omega_sum weight repair, all normals retained.
This serves the genuine dB defect and exports the ENTIRE new endpoint packet.
"""
from pathlib import Path
import sympy as s,json
U,R,W,t,rho,kappa,z=s.symbols('U R W t rho kappa z',nonzero=True)
d=t/(4*rho);r=R-d;H=1+U*U-R*R+2*d*R;K=r*r-U*U
kt=-3*kappa/(t*rho*rho);dt=-(t**3+1)/(4*rho**3)
DU=lambda f:s.diff(f,U)+U/W*s.diff(f,W)
DR=lambda f:s.diff(f,R)+z/(3*R)*s.diff(f,z)-kappa*R/W*s.diff(f,W)
DT=lambda f:s.diff(f,t)+3*t*t/rho*s.diff(f,rho)+kt*s.diff(f,kappa)-t*t*z/rho**2*s.diff(f,z)-kt*R*R/(2*W)*s.diff(f,W)
def red(f):
 n=s.cancel(f).as_numer_denom()[0]
 n=s.rem(n,W*W-U*U+kappa*R*R,W)
 n=n.subs(kappa,4*t**3/rho**2)
 n=s.together(n).as_numer_denom()[0]
 return s.factor(s.rem(n,rho*rho-2*t**3+1,rho))
B=U/W-1
# At fixed(t,psi), r/U is fixed; at fixed(H,psi), d(H)=0.
BH=s.factor(-(U*DU(B)+r*DR(B))/(2*K))
Bt=s.factor(DT(B)+U*d*dt/K*DU(B)+(1+r*d/K)*dt*DR(B))
BHclosed=kappa*R*U*d/(2*K*W**3)
ratio=-3*K*R/(t*rho**2*d)+2*(t**3+1)*(H-1)/(t*rho**2)
checks={'actual_B_H_at_fixed_Psi':red(BH-BHclosed)==0,'actual_B_t_over_B_H_at_fixed_Psi':red(Bt-ratio*BH)==0}
At=t*H*(H-1)/rho;AH=-t*t*rho/3
r0=rho**3/(36*t)*(3*K*R/d-(H-1)*(3*H+2*t**3+2))
checks['forced_r0_has_no_new_normal_divisor']=red((At-ratio*AH)-r0*kt)==0
# All coefficients of psi=dlog[(r+U)/(r-U)] in (t,U,R).
psi=[2*U*dt/K,2*r/K,-2*U/K]
dB=[DT(B),DU(B),DR(B)]
dH=[2*R*dt,2*U,-2*r]
K0=[At+AH*dH[0],AH*dH[1],AH*dH[2]]
def wedge3(a,b,c):
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
checks['WHOLE_actual_descended_base_wedge']=red(wedge3(dB,K0,psi)-r0*wedge3(dB,[kt,0,0],psi))==0
P=3*U*(U+W)/(16*R**2);OU=2*DU(P);OR=2*DR(P)
checks['FULL_Omega_UR_closed']=red(DU(OR)-DR(OU))==0
checks['FULL_Omega_tU_curvature']=red(DT(OU)+s.Rational(3,16)*kt*DU(B))==0
checks['FULL_Omega_tR_curvature']=red(DT(OR)+s.Rational(3,16)*kt*DR(B))==0
EG=kappa*(3+2/B)
checks['FULL_Omega_exact_split_U']=red(OU-s.Rational(3,16)*DU(EG))==0
checks['FULL_Omega_exact_split_R']=red(OR-s.Rational(3,16)*DR(EG))==0
checks['FULL_Omega_exact_split_t']=red(s.Rational(3,16)*(B*kt+DT(EG)))==0
Lcurv=6*H+7*t**3-5
checks['WHOLE_descended_CM_curvature_tU']=red(DT(K0[1])-DU(K0[0])+t*Lcurv/(3*rho)*dH[1])==0
checks['WHOLE_descended_CM_curvature_tR']=red(DT(K0[2])-DR(K0[0])+t*Lcurv/(3*rho)*dH[2])==0
checks['WHOLE_descended_CM_curvature_UR']=red(DU(K0[2])-DR(K0[1]))==0
HH=s.symbols('HH')
DD=HH-2*t**3
checks['WHOLE_retained_CM_source_amplitude']=s.factor(1+2*(6*HH+7*t**3-5)/DD-(13*HH+12*t**3-10)/DD)==0
assert all(checks.values()),checks
out={
 'status':'ONE_EXPLICIT_ACTUAL_DESCENDED_Y_CM_GREEN_WEIGHT_REPAIR; ENTIRE_REMAINDER_RETAINED',
 'source_Y_sign':'dJY=beta+RY*mu*theta0, RY=−B*Ppoly/(108A²),mu=etaCM dUdr. Thus beta−dJY is POSITIVE B*Ppoly*mu*theta0/(108A²), and the source-bound CM repair has +mY KP, dKP=+t etaCM omegaQ.',
 'physical_field':'d=t/(4rho),r=R−d,H=1+U²−R²+2dR,K=r²−U²,H0=1+d²,R=rho z³,rho²=2t³−1,kappa=4t³/rho²,W²=U²−kappa R²,C=tz²/3+z(U+W)/4.',
 'actual_descended_CM_amplitude':'B=U/W−1,A=3(U²−1)−3(2t³+3)z⁶−tz³,Ppoly=−12U²−6+(24t³−72)z⁶−tz³,Dmix=H−2t³,F0=Ppoly/(72tA²Dmix).',
 'CM_base_form':'K0=tH(H−1)etaCM−(t²rho/3)dH; etaCM=dt/rho. The FULL normalized h,y,rho trace is JCMdesc=B*F0*K0 wedge psi wedge theta0,psi=dlogPsi; the extra y-trace cochain vanishes under the actual rho deck (authoritative source-incidence receipt).',
 'actual_source_normals':'B_H|t,Psi=kappa R U d/(2K W³). B_t|H,Psi / B_H=−3KR/(t rho² d)+2(t³+1)(H−1)/(t rho²). No W,z normal is frozen.',
 'ONE_forced_coefficient':'r0=rho³/(36t)*[3KR/d−(H−1)(3H+2t³+2)]. This is W-even and has no new B_H or other normal divisor.',
 'WHOLE_actual_wedge':'dB wedge K0 wedge psi = r0*dB wedge dkappa wedge psi. This is verified with all physical t,U,R components, including the t leg of psi.',
 'Omega_sum':'Omega=2DU(P_high)dU+2DR(P_high)dR, P_high=3U(U+W)/(16R²). FULL dOmega=(3/16)dB wedge dkappa.',
 'ONE_literal_repair':'JG=−(16/3)*F0*r0*Omega wedge psi wedge theta0.',
 'WHOLE_literal_derivative':'dJG=−F0*dB wedge K0 wedge psi wedge theta0 −(16/3){d(F0r0) wedge Omega wedge psi wedge theta0+F0r0*Omega wedge psi wedge(dH wedge thetaH+dC wedge thetaC)}.',
 'WHOLE_descended_CM_curvature':'dK0=−t(6H+7t³−5)*etaCM wedge dH/3. It is not silently identified with the Y source after a nonconstant weighted trace.',
 'WHOLE_extra_hol_source_curvature_packet':'RYsource−B*F0*dK0 wedge psi = B*Ppoly*(13H+12t³−10)*mu/[108A²Dmix],mu=etaCM wedge dU wedge dr. This multiplies theta0 and MUST remain in addition to the next two packets.',
 'WHOLE_remaining_after_Y_CM_and_Green':'B*Ppoly*(13H+12t³−10)*mu*theta0/[108A²Dmix] +{−B*dF0 wedge K0+(16/3)d(F0r0) wedge Omega} wedge psi wedge theta0 +F0{−B*K0+(16/3)r0*Omega} wedge psi wedge(dH wedge thetaH+dC wedge thetaC). None of these THREE packets is asserted zero.',
 'FULL_exact_split':'Omega=(3/16)[B dkappa+dE_G],E_G=kappa(3+2/B). Thus the curvature repair is an explicit normal-coordinate current; its curvature alone is not a proof of new closure.',
 'endpoint':'theta0=dp/Z,thetaH=−(H+Cp)dp/Z³,thetaC=−p(H+Cp)dp/Z³. These are literal forms, with all compact rows and fiber cochains retained.',
 'scope':'One genuine source-weight derivative component is served by a concrete rational current. The derivative of its weight and all endpoint transport remain explicit, for the fixed-S Clow_R / rank4 correction. No certificate claimed.',
 'checks':checks,'check_count':len(checks)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual descended Y/CM omega_sum repair and FULL physical base wedge')
