"""Whole original source binding for the full-t derivative Green pair.
No endpoint primitive is inferred from the exact source transport.
"""
from pathlib import Path
import sympy as s,json
U,R,W,t,rho,kap,z=s.symbols('U R W t rho kappa z',nonzero=True)
P=3*U*(U+W)/(16*R*R)
kapt=-3*kap/(t*rho*rho)
TW=-9*kap/(32*t*rho*rho)
TU=-9*kap*(2*U-W)/(32*t*rho*rho*W)
DU=lambda f:s.diff(f,U)+U/W*s.diff(f,W)
DR=lambda f:s.diff(f,R)+z/(3*R)*s.diff(f,z)-kap*R/W*s.diff(f,W)
DT=lambda f:s.diff(f,t)+3*t*t/rho*s.diff(f,rho)-t*t*z/rho**2*s.diff(f,z)+kapt*s.diff(f,kap)-kapt*R*R/(2*W)*s.diff(f,W)
def red(f):
 n=s.cancel(f).as_numer_denom()[0]
 return s.factor(s.rem(n,W*W-U*U+kap*R*R,W))
logLU=3*DU(U+W)/(U+W)
logLR=3*DR(U+W)/(U+W)+1/R
logLt=3*DT(U+W)/(U+W)
checks={
 'TW_dt_is_three_over_32_dkappa':s.factor(TW-s.Rational(3,32)*kapt)==0,
 'TU_dt_split':s.factor(TU-(3*U/(16*W)-s.Rational(3,32))*kapt)==0,
 'FULL_difference_has_no_dt_component':red(kap*logLt/8+s.Rational(3,16)*(U/W-1)*kapt)==0,
 'FULL_sum_dt_cancellation':red(2*DT(P)+3*U*kapt/(16*W))==0,
}
x,y,zz=s.symbols('x y zz',nonzero=True)
txy=x*y/zz**2
Uxy=x**3+y**3;Wxy=x**3-y**3
# rho(t) derivative is retained by chain rule in R=rho(t)*z^3.
trow=[s.diff(txy,k)for k in(x,y,zz)]
Urow=[s.diff(Uxy,k)for k in(x,y,zz)]
Rrow=[3*txy*txy/rho*trow[j]*zz**3+(3*rho*zz*zz if j==2 else 0)for j in range(3)]
Jac=s.factor(s.det(s.Matrix([trow,Urow,Rrow])))
checks['WHOLE_original_jacobian']=s.factor(Jac+9*rho*Wxy)==0
checks['WHOLE_original_A_unit']=s.factor(y**3/(-9*rho*Wxy)+(Uxy/Wxy-1)/(18*rho))==0
# beta = (y^3 dxdy dz)*thetaH/6, F-first residue convention.
checks['WHOLE_Green_difference_source_unit']=s.factor(-s.Rational(1,108)/rho - (rho**3/(243*t*t))*s.Rational(3,16)*(-12*t*t/rho**4))==0
# logL source formula uses kappa=4t^3/rho^2.
checks['WHOLE_logL_source_unit']=red(-t*rho*logLt/486+(U/W-1)/(108*rho)).subs(kap,4*t**3/rho**2)==0
assert all(checks.values()),checks
out={
 'status':'PASS_WHOLE_ORIGINAL_SOURCE_BOUND_FULL_T_DUAL_GREEN_PACKET; ENDPOINT_CLOSURE_OPEN',
 'physical_field':'t=xy/z²,rho²=2t³−1,R=rho*z³,U=x³+y³,W=x³−y³,kappa=4t³/rho²,P=3U(U+W)/(16R²),Lmono=(U+W)^3 R',
 'source_convention':'Original affine Ω=dx de dy dz df=dx dy dz de df. Choose dF first in the double-pole residue. Then beta_original=(y³ dxdy dz) wedge theta_H/6, theta_H=−(H+Cp)dp/Z³.',
 'WHOLE_original_source':'beta_original=−(U/W−1)*etaCM wedge dU wedge dR wedge theta_H/108, etaCM=dt/rho.',
 'FULL_derivative_Green_U':'omega_U=d[P−3kappa/32]+kappa*dlogLmono/16+(3U/(16W))*dkappa',
 'FULL_derivative_Green_W':'omega_W=d[P+3kappa/32]−kappa*dlogLmono/16',
 'FULL_difference':'omega_U−omega_W=kappa*dlogLmono/8+(3/16)(U/W−1)*dkappa',
 'FULL_sum':'omega_U+omega_W=2dP+(3U/(16W))*dkappa',
 'WHOLE_source_binding':'beta_original=rho³/(243t²)*(omega_U−omega_W−kappa*dlogLmono/8) wedge dU wedge dR wedge theta_H',
 'equivalent_source_log_packet':'beta_original=−t*rho*dlogLmono wedge dU wedge dR wedge theta_H/486. The omega_U/W wedge dU wedge dR terms vanish since those Green forms are defined with only U,R legs; this is source transport, not a primitive.',
 'normalizations':'dkappa=−12t²dt/rho⁴; all physical t normals of z,W,rho,kappa are retained. Original source is entire signed U/W channel combination, not one channel alone.',
 'remaining':'Construct an actual endpoint-coupled current using the full Green/CM-projector packet. No scalar logarithm or primitive of etaCM is silently allowed.',
 'checks':checks,'check_count':len(checks)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'whole-source dual Green packet with full-t normals')
