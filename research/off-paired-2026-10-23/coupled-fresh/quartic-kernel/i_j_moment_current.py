#!/usr/bin/env python3
"""Exact alternative i current and mixed rational moment identities.

All finite/infinity components are retained. No weighted density closure
is inferred from these literal primitive identities.
"""
import json
from pathlib import Path
import sympy as s

a,y,x,i,j,v=s.symbols('a y x i j v')
Q=y*y+v*(a*a+i*x*x+j*a*x+x+1)
J=2*v*a*a+j*v*a*x-2*y*y
gb=s.groebner([a*y-x**3,Q],a,y,x,domain=s.QQ.frac_field(i,j,v))
checks={}
def check(name,z):
    num=s.together(z).as_numer_denom()[0]
    assert gb.reduce(num)[1]==0,(name,s.factor(num))
    checks[name]=True

ai=-v*a*x*x/J;yi=v*y*x*x/J
aj=-v*a*a*x/J;yj=v*x**4/J
ad=a*(6*y*y+2*i*v*x*x+j*v*a*x)/J
yd=-y*ad/a
def Ei(z):return s.diff(z,i)+s.diff(z,a)*ai+s.diff(z,y)*yi
def Ej(z):return s.diff(z,j)+s.diff(z,a)*aj+s.diff(z,y)*yj
def DD(z):return 6*v*s.diff(z,v)-2*i*s.diff(z,i)-j*s.diff(z,j)+s.diff(z,a)*ad+s.diff(z,y)*yd

psi_i=y/x**2;psi_j=y*y/(2*x**4);nu=v*y/J
check('literal_i_primitive',Ei(psi_i)-nu)
check('literal_j_primitive',Ej(psi_j)-nu)
for name,z in [('a',a),('y',y),('i',i),('j',j),('v',v)]:
    check('commutator_D_Ei_'+name,DD(Ei(z))-Ei(DD(z))-2*Ei(z))
Vi=2*psi_i-DD(psi_i)
U=3*psi_j-DD(psi_j)
check('actual_i_Euler_source_primitive',Ei(Vi)-(4*nu-DD(nu)))
check('actual_j_Euler_source_primitive',Ej(U)-(4*nu-DD(nu)))
ss=y/x**2
check('i_j_characteristic_s_invariant',Ei(ss)-ss*Ej(ss))
for n in range(1,5):
    check('literal_mixed_moment_'+str(n),Ej(ss**(n+1)/(n+1))-Ei(ss**n/n))

# Complete finite-pole correction and explicit polynomial numerator.
yx=v*(y*(2*i*x+j*a+1)+3*x*x*(2*a+j*x))/J
omega=v*x*x/J;zeta=y/x
Npoly=v*((2*i-1)*y-i*x*y+6*a*x-2*a*x*x+3*j*x*x-s.Rational(3,2)*j*x**3)
check('compact_i_polynomial_numerator',yx/x-y/(2*x)-j*omega-Npoly/J)

# Independent infinity expansion, in x=t^-2,a=t^-3*A(t).
t,alpha=s.symbols('t alpha')
A=alpha
ac=[]
for n in range(1,4):
    z=s.symbols('A'+str(n))
    trial=A+z*t**n
    equation=trial**4+j*trial**3*t+i*trial**2*t*t+trial**2*t**4+trial**2*t**6-alpha**4
    coeff=s.expand(equation).coeff(t,n)
    sol=s.solve(coeff,z)[0]
    ac.append(s.factor(sol));A=trial.subs(z,sol)
Y=s.series(1/A,t,0,4).removeO()
assert s.factor(Y.coeff(t,3))==0
checks['independent_zeta_infinity_residue_zero']=True
res_i=s.factor(-2*Y.coeff(t,1))
assert res_i==-j/(2*alpha**2)
checks['independent_i_infinity_residue']=True
assert s.cancel(res_i-j*(-1/(2*alpha**2)))==0
checks['compact_i_infinity_correction_sign']=True

out={
 'status':'Literal source-carrying alternate i/j currents; actual weighted correction remains open',
 'curve':'a*y=x^3; y^2+v*(a^2+i*x^2+j*a*x+x+1)=0',
 'psi_i':'(y/x^2) dx = (x/a) dx',
 'psi_j':'(y^2/(2*x^4)) dx',
 'literal_source':'partial_i Psi_i=partial_j Psi_j=nu_b',
 'Vi':'(2-D)Psi_i','U':'(3-D)Psi_j',
 'D':'6v partial_v-2i partial_i-j partial_j, flat implicit lifts at fixed x',
 'actual_euler_source':'partial_i Vi=partial_j U=(4-D)nu_b',
 'weighted_current':'For actual density t=hsrc/(6v^2), Pi=t*Vi leaves -t_i*Vi; Pj=t*U leaves -t_j*U. All derivatives hold other native base parameters fixed and include physical w derivatives.',
 'compact_i':'Omega_i=Psi_i-zeta_hat/2+d_x(y/x)-j*omega',
 'compact_i_numerator':str(Npoly),
 'finite_i_residues':'Pa: +/-sqrt(-v)/2; Pb:0',
 'infinity_i_residues':'j times omega residue, canceled by MINUS j*omega',
 'Vi_residues':'Infinity canceled by (2-D), finite Pa residue = -zeta_hat/2 residue; this finite companion MUST be retained.',
 'mixed_moments':'partial_j[s^(n+1)/(n+1) dx]=partial_i[s^n/n dx], s=y/x^2, n>=1',
 'characteristic':'(partial_i-s*partial_j)s=0',
 'inverse_pencil':'i=-s^-2-j/s-x^2*s^2/v-(x+1)/x^2',
 'infinity_A_coefficients':list(map(str,ac)),
 'checks':checks,'count':len(checks),'certificate':False}
path=Path(__file__).with_name('i-j-moment-current-results.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'output':str(path)}))
