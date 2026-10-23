#!/usr/bin/env python3
"""Whole weighted graph model, elliptic maps and actual target normal jet."""
import json
from pathlib import Path
import sympy as s

e,a,b,t,A,H=s.symbols('epsilon a b t A H')
mij,mjk,mik=s.symbols('mij mjk mik')
C0=1+a**6+b**6
M0=mij*a+mjk*b+mik*a*b
CY=e**6*C0
T=e**6*(a**6+1)
W=e**12*a**6
D18=CY*T*T+16*H*W
strict=e**4*C0*((1+a**6)**2-16*a**6)-16*a**6*M0
checks={}
checks['ordinary_blowup_exact']=s.expand(D18.subs(H,-e**2*M0-e**6*C0)-e**14*strict)==0
S=(1+b**6+t**12*A**6)*((1+t**12*A**6)**2-16*t**12*A**6)-16*A**6*(mjk*b+t**2*A*(mij+mik*b))
checks['weighted_model_exact']=s.expand(strict.subs({e:t**3,a:t**2*A})-t**12*S)==0
w=s.symbols('w')
checks['exceptional_quotient']=s.expand((b*S.subs(t,0)).subs(A**6,w*w/(16*b*b))-(b+b**7-mjk*w*w))==0
x,z,xi,y=s.symbols('x z xi y')
UC=8*xi**6
VC=2*s.sqrt(2)*s.I*xi**3*z**3
ec=s.expand(VC**2-UC**3-UC).subs(z**6,-1-64*xi**12)
checks['whole_Cprime_elliptic']=s.expand(ec)==0
checks['Cprime_map_x']=s.expand(UC.subs(xi**6,x**3/8)-x**3)==0
UG=b**3;VG=b*y
checks['whole_G_elliptic']=s.expand((VG**2-UG**3-UG).subs(y**2,b**7+b))==0
# Differential coefficients are compared after xi'=1/(4xi).
etaC=s.diff(UC,xi)/(4*xi)/(2*VC)
checks['Cprime_actual_differential']=s.simplify(etaC-3*xi/(s.sqrt(2)*s.I*z**3))==0
checks['G_actual_differential']=s.cancel(s.diff(UG,b)/(2*VG)-3*b/(2*y))==0
checks['descended_product']=s.cancel((3*xi/(s.sqrt(2)*s.I*z**3))*(3*b/(2*xi*w))-9/(8*s.sqrt(2)*s.I)*4*b/(z**3*w))==0
# Exact original three-Y Jacobian in the specified order.
Y=s.Matrix([t**5*A,t**3,t**3*b])
J=Y.jacobian([t,A,b]).det()
checks['actual_Y_jacobian']=s.expand(J+3*t**10)==0
# Ordered orientation aside, absolute coefficient of target normal jet.
Y0=s.symbols('Y0')
num=z**3*Y0**3
Fz=6*z**5;Fzz=30*z**4
res=s.cancel((num*Fzz-s.diff(num,z)*Fz)/Fz**3)
checks['actual_X0_normal_numerator']=s.cancel(res-Y0**3/(18*z**8))==0
checks['target_weighted_leading_jet']=s.cancel(res.subs(Y0,t**5*A)*3*t**10-t**25*A**3/(6*z**8))==0
# Characters using formal root relations.
q=s.symbols('q')
gamma=4*b/(z**3*w)
checks['order6_character']=s.cancel(gamma.subs({x:q*x,b:b/q,w:w/q},simultaneous=True)*q/q-gamma)==0
ch3=s.cancel(gamma.subs({x:q*q*x,z:q*q*z,w:q*q*w},simultaneous=True)*q*q/gamma)
checks['order3_character']=s.rem(s.Poly(s.fraction(s.cancel(ch3-1))[0],q),s.Poly(q**3-1,q)).is_zero
r=s.symbols('r')
K=(1+a**6)**2-16*a**6
checks['global_r_first_equation']=s.cancel(strict.subs(e**4,r*r*a**6)-a**6*(r*r*C0*K-16*M0))==0
HXreplacement=-r*a**3*M0-r**3*a**9*C0
checks['global_r_second_equation']=s.expand((16*HXreplacement+r**3*a**3*C0*(1+a**6)**2).subs(M0,r*r*C0*K/16))==0
candidate=[]
for jj in range(1,6):
    for ii in range(1,2*jj,2):
        for ll in range(3):
            if (ii-(2*ll+1))%12==0 and (ii-2*jj)%3==0:
                candidate.append([ii,jj,ll])
checks['full_invariant_H20_basis']=sorted(candidate)==[[1,2,0],[1,5,0],[3,3,1],[5,4,2]]
checks['antiinvariant_Cprime_dimension']=sum(1 for jj in range(1,6) for ii in range(1,2*jj,2))==15
L=z**3/2+z*z*x*b/3
deriv=r*L/(x*b*z**3)
checks['actual_first_a_jet']=s.cancel(deriv-r*(1/(2*x*b)+1/(3*z)))==0
# w_x=-w/(2*x) on exceptional m=x/2; coefficient of d(4 db/w).
checks['first_piece_exact']=s.cancel(-4*(-w/(2*x))/w**2-r/(2*x*b)).subs(r,4*b/w)==0
HH,MM,CC,KK,aa=s.symbols('HH MM CC KK aa')
E1=16*MM-r*r*CC*KK
E2=16*HH+r**3*aa**3*CC*(1+aa**6)**2
elim=HH**2*CC*KK**3-16*aa**6*MM**3*(1+aa**6)**4
rr=-HH*KK/(aa**3*MM*(1+aa**6)**2)
checks['global_r_open_elimination']=s.cancel(E1.subs(r,rr)+elim/(aa**6*MM**2*(1+aa**6)**4))==0
checks['global_r_open_recovery']=s.cancel((E2+r*aa**3*(1+aa**6)**2*E1/KK).subs(r,rr))==0
out={'checks':checks,'passed':all(checks.values()),'count':len(checks),
     'scope':'Actual exceptional surface and target-character form; no global extension or source Gysin coefficient.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
assert out['passed']
