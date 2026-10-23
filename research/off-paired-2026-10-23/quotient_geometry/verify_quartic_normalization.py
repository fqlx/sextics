from pathlib import Path
import json
import sympy as s
u,v,w,e,S,q,k,t=s.symbols('u v w e S q k t')
G=v**4+S*v**2+e*u**3*v+u**6
F=v**2+w**2+e*w+S
checks={}
checks['quartic_clearing']=s.rem(s.expand(v**2*F-G),v*w-u**3,w)==0
D=256*u**12+(-128*S**2+144*S*e**2-27*e**4)*u**6+16*S**4-4*S**3*e**2
checks['normalized_discriminant']=s.expand(s.discriminant(G,v)-u**6*D)==0
J0=4*v**2+e*w+2*S
J2=2*v**2-2*w**2-e*w
checks['actual_normal_F'] = s.cancel((v/J2)*s.diff(F,v)-(w/J2)*s.diff(F,w)-1)==0
checks['actual_normal_toric'] = s.cancel((v/J2)*s.diff(v*w-u**3,v)-(w/J2)*s.diff(v*w-u**3,w))==0
checks['normal_jet_relation']=s.expand(J2-J0+2*F)==0
res=(4*v**3*s.diff(G,v)-v**4*s.diff(G,v,2))/(3*s.diff(G,v)**3)
resN=v*(4*v**2+4*e*w+6*S)/(3*J0**3)
num=s.together(res-resN).as_numer_denom()[0]
GB=s.groebner([v*w-u**3,F],w,v,u,S,e,order='lex')
checks['actual_residue_source']=GB.reduce(num)[1]==0
m=s.symbols('m')
resolvent=m**3+2*S*m**2+(S**2-4*u**6)*m-e**2*u**6
r0=(S+q**2-e*u**3/q)/2
s0=(S+q**2+e*u**3/q)/2
prod=s.expand((v**2+q*v+r0)*(v**2-q*v+s0)-G)
checks['Ferrari_resolvent']=s.cancel(prod-resolvent.subs(m,q**2)/(4*q**2))==0
qt=e*(t-1/t)/4;kt=e*(t+1/t)/2
checks['resolvent_conic']=s.cancel(kt**2-4*qt**2-e**2)==0
assert all(checks.values()),checks
out={'checks':checks,'status':'Exact normal model, second-pole source and finite correspondence; no primitive.'}
Path(__file__).with_name('quartic-normalization-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
