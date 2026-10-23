"""Actual J=1 source projection, including the change-of-lift primitive.

This verifies a source-carrying elliptic normal component and the full
Prym component.  It does not assert a closed mixed Gysin current.
"""
import json
from pathlib import Path
import sympy as s
a,t,b,c,d,e,m=s.symbols('a t b c d e m',nonzero=True)
Ja=2*a*a+d*a-2*b*b
Jt=2*t*t+e*t-2*b*b
D1=2*a*a+d*a-2*t*t-e*t
ae=-a*t/D1;te=t*t/D1
ab=a*Jt/(b*D1);tb=-t*Ja/(b*D1)
eta=1/D1
parE=lambda f:s.diff(f,e)+ae*s.diff(f,a)+te*s.diff(f,t)
db=lambda f:s.diff(f,b)+ab*s.diff(f,a)+tb*s.diff(f,t)
tauB=-parE(eta)
H=b*t/(Ja*D1)
tauQ=-2*t*(3*a*a+d*a+b*b)/(Ja**2*D1)
checks={}
checks['actual_chart_eta_orientation']=s.cancel(-b*tb/(t*Ja)-eta)==0
checks['fixed_q_fixed_b_exact_primitive']=s.factor(s.together(tauB-db(H)-tauQ))==0

Y=2*(a+t)+m
z=a-t
onD=tauB.subs({d:m,e:m})
swap=lambda f:f.xreplace({a:t,t:a})
plus=s.factor((onD+swap(onD))/2)
minus=s.factor((onD-swap(onD))/2)
checks['actual_elliptic_source_component']=s.factor(plus-1/Y**3)==0
checks['actual_prym_source_component']=s.factor(minus+((a+t)**3+2*m*a*t)/(z**3*Y**3))==0
checks['eta_is_anti_invariant']=s.factor((eta+swap(eta)).subs({d:m,e:m}))==0
etaell=(a-t)*eta/b
checks['quotient_holomorphic_form_invariant']=s.factor((etaell-swap(etaell)).subs({d:m,e:m}))==0
HD=H.subs({d:m,e:m})
Hp=s.factor((HD+swap(HD))/2);Hm=s.factor((HD-swap(HD))/2)
checks['both_actual_Cartan_projections_retained']=s.factor(Hp+Hm-HD)==0

ss,zz=s.symbols('s zeta',nonzero=True)
quartic=-4*b**4+(m*m-4*c)*b*b+8*b
Qred=ss*ss+m*ss+b*b+c-2/b
checks['elliptic_quotient_equation']=s.expand(b*b*(2*ss+m)**2-quartic-4*b*b*Qred)==0

u,L,y=s.symbols('u lambda y',nonzero=True)
P=8*u**3+L*u*u-4
Delta=L**3-1728
ellsource=-u/y**3
psi=1/(u*y)
parL=lambda f:s.diff(f,L)+u*u*s.diff(f,y)/(2*y)
checks['literal_elliptic_section_primitive']=s.factor(2*parL(psi)-ellsource)==0
R=(L*L-12*L*u-288*u*u)/Delta
dy=lambda f:s.diff(f,u)+s.diff(P,u)*s.diff(f,y)/(2*y)
reduced=12*L/Delta/y+144*u/Delta/y+dy(R/y)
class_numerator=s.together(ellsource-reduced).as_numer_denom()[0]
checks['complete_rank_two_elliptic_source_class']=s.factor(s.rem(class_numerator,y*y-P,y))==0

# Physical J=1 slice: A=k^2*T, hence the involution a<->t/k is rational
# before adjoining normalized square/sixth roots.
k,zphys,T,B,S=s.symbols('k zphys T B S',nonzero=True)
Qphysical=T*(S*S-2*k/b)+B*b*b+k/3+zphys*S/2
Wphysical=b*(2*T*S+zphys/2)
Ephysical=-4*T*B*b**4+(zphys*zphys/4-4*k*T/3)*b*b+8*k*T*T*b
checks['physical_source_quotient_with_all_coefficients']=s.expand(Wphysical**2-Ephysical-4*T*b*b*Qphysical)==0
rho,rr=s.symbols('rho r',nonzero=True)
cmk=(rr+1/rr)/(2*rho)
cmr=(rr-1/rr)/2
checks['physical_CM_base_cover_conic']=s.factor(cmr*cmr+1-cmk*cmk*rho*rho)==0

assert all(checks.values()),checks
out={
 'status':'Actual J=1 elliptic/Prym source split and explicit elliptic normal-function derivative; mixed Gysin closure open',
 'checks':checks,'passed':True,'certificate':False,
 'normal_coordinates':'d=m+n,e=m-n; n=(d-e)/2, J=(d/e)^2=1 on the chosen d=e component',
 'quotient':'W^2=-4b^4+(m^2-4c)b^2+8b, W=b(2s+m), s=a+t',
 'actual_form_orientation':'eta_b=b*dq/J in t=1 chart equals +db/[zeta*(2s+m)] in q=1 chart, zeta=a-t',
 'fixed_b_source_split':{'elliptic_plus':'db/(2s+m)^3=b^3*db/W^3',
                        'Prym_minus':'-(s^3+2m/b)*db/[zeta^3*(2s+m)^3]'},
 'actual_fixed_q_fiber_primitive':'tau_actual=tau_fixed_b-d_b H, H=b*t/[J_a*(a(2a+d)-t(2t+e))], J_a=2a^2+d*a-2b^2',
 'projected_fiber_primitives':{'plus':str(Hp),'minus':str(Hm)},
 'elliptic_weierstrass':'u=1/b,y=W/b^2, y^2=8u^3+lambda*u^2-4, lambda=m^2-4c',
 'elliptic_actual_source':'tau_plus=-u*du/y^3',
 'elliptic_source_primitive':'psi=du/(u*y); tau_plus=2*partial_lambda psi literally; finite residues at(u=0,y=±2sqrt(-1)) are±1/(2sqrt(-1)); no infinity residue',
 'elliptic_rank_two_class':'tau_plus=(12lambda/Delta)*du/y+(144/Delta)*u*du/y+d_u[(lambda^2-12lambda*u-288u^2)/(Delta*y)], Delta=lambda^3-1728',
 'physical_quotient':'Wphys^2=-4*T*B*b^4+(z^2/4-4*k*T/3)*b^2+8*k*T^2*b; T=1+z^6,B=1+k^6/r^2,r^2=k^2*T-1',
 'physical_CM_cover':'rho^2=1+z^6, k=(rpar+rpar^-1)/(2rho), r=(rpar-rpar^-1)/2; cover is genus2(z,rho) times rational rpar line',
 'remaining':'Elliptic projection alone does not serve the nonzero Prym source. A closed mixed two-form on the support divisor, its normal/Gysin source identity, full physical normalizers/density, and a current for every complementary component remain required.'
}
Path(__file__).with_name('j1-source-projection-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'Passed {len(checks)} exact J1/source/elliptic-current identities')
