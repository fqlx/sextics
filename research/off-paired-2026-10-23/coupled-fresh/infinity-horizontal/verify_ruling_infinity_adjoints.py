"""Physical scalar connection of the rational infinity companion."""
import json
from pathlib import Path
import sympy as s
R,S,z,k=s.symbols('R S z k',nonzero=True)
A=1+R;B=1+S;E=z/2;D=z*k/2;T=1+z**6
Cp=k/3-z*z*k*k/(16*A)
ca=2-1/R-3/S;cz=-6+4/R+2/S;t=6*z**6/T
def lift(PT,sE):
    const=sE*(-2*(1+1/R)-4*(1+1/S)+12)
    Z=s.factor((ca*PT/T-const)/(ca*t+cz))
    alpha=s.factor(t*Z-PT/T)
    v=s.factor(s.Rational(3,2)*(alpha-Z+sE))
    u=s.factor(-Z-v/3)
    return {'R':s.factor(A*(alpha-2*u-2*v)),
            'S':s.factor(B*(alpha+2*u-2*v)),
            'z':s.factor(z*Z),'alpha':alpha,'u':u,'v':v}
def dR(f):return s.diff(f,R)+k*s.diff(f,k)/(6*R)
def dS(f):return s.diff(f,S)+k*s.diff(f,k)/(6*S)
def act(V,f):return V['R']*dR(f)+V['S']*dS(f)+V['z']*s.diff(f,z)
def div(V):return dR(V['R'])+dS(V['S'])+s.diff(V['z'],z)-s.Rational(5,6)*(V['R']/R+V['S']/S)
VEs=lift(0,1/E)
Y=lift(E/(2*Cp),1/E)
cpsi=-2*Y['u']+s.Rational(2,3)*Y['v']
comega=-Y['alpha']+2*Y['v']
g=3*A*E/Cp
f=-2*Cp/D
ME=s.factor(div(VEs)-VEs['alpha']-VEs['u']+s.Rational(5,3)*VEs['v'])
checks={
  'physical_g_connection':s.factor(act(Y,g)-3*A/Cp-(cpsi-comega)*g)==0,
  'raw_infinity_adjoint':s.factor(f*(act(Y,g)+g*(comega-cpsi))+6*A/D)==0,
}
assert all(checks.values()),checks
out={'checks':checks,'passed':True,'ME':str(ME),
     'ME_at_1':str(ME.subs({R:1,S:1,z:1,k:1})),
     'raw_omega_residue':'-(6*A/D)*ME',
     'certificate':False}
Path(__file__).with_name('ruling-infinity-adjoints-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
