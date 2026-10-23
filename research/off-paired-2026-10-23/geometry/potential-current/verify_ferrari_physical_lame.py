from pathlib import Path
import json
import sympy as s
u,e,S,z,p,h,Z=s.symbols('u e S z p h Z')
U=-S*e/(12*u**2)
E=(4*u**6-S**2+S*e**2/4)/u**3
P=2*E/z
f=z/2+p/3
G=3*e*u**3-f*U-u*P/3
MZ=(h*G-12*p**5*P)/Z
d=2*S*e/(3*u**3)-(h*G-12*p**5*P)/Z**2
checks={'physical_integrating_factor':s.cancel(d+8*U/u+MZ/Z)==0}
q,S,T,lam=s.symbols('q S T lam')
checks['second_order_lame']=s.expand((-q**3-2*S*q)+(4*S/3+lam)*q).subs(lam,q**2+2*S/3).expand()==0
q0,q1,V,mu=s.symbols('q0 q1 V mu')
r0,r1,r2,r3,d0,d1,d2=s.symbols('r0 r1 r2 r3 d0 d1 d2')
# Div_phys(mu*(q r1-q1 r0)M); M(mu)=-d mu and M2(q)=-Vq.
left=-d0*mu*(q0*r1-q1*r0)+mu*(q0*r2+V*q0*r0)+d0*mu*(q0*r1-q1*r0)
checks['second_order_physical_concomitant']=s.expand(left-mu*q0*(r2+V*r0))==0
# Third-order Green identity checked with independent jets.
Dr=r1+d0*r0
D2r=r2+2*d0*r1+(d1+d0*d0)*r0
D3r=r3+3*d0*r2+(3*d1+3*d0*d0)*r1+(d2+3*d0*d1+d0**3)*r0
J=q0*D2r-q1*Dr-q0**3*r0
q2=-q0**3-2*S*q0
MDr=r2+d1*r0+d0*r1
MD2r=r3+2*d0*r2+(3*d1+d0*d0)*r1+(d2+2*d0*d1)*r0
MJ=q1*D2r+q0*MD2r-q2*Dr-q1*MDr-3*q0*q0*q1*r0-q0**3*r1
expr=s.expand(MJ+d0*J-q0*(D3r+2*S*Dr+3*T*r0)).subs(q1,-T/q0)
checks['third_order_physical_concomitant']=s.cancel(expr)==0
assert all(checks.values()),checks
out={'checks':checks,'status':'Exact conditional physical current identities; scalar forcing remains unsolved.'}
Path(__file__).with_name('ferrari-physical-lame-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
