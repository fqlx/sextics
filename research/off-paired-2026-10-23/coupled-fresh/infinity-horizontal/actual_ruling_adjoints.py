"""Actual-base T/shear lifts and density adjoints for ruling source transport."""
import sympy as s,json
from pathlib import Path
R,S,z,k=s.symbols('R S z k',nonzero=True)
TT=1+z**6;aa=1+R;bb=1+S;t=6*z**6/TT
ca=2-1/R-3/S;cz=-6+4/R+2/S;den=ca*t+cz

def lift(PT=0,sC=0,sD=0,sE=0):
 const=sC*(2*(1+1/R)-2*(1+1/S)-6)+sD*(-2*(1+1/R)+2*(1+1/S))+sE*(-2*(1+1/R)-4*(1+1/S)+12)
 Z=s.factor((ca*PT/TT-const)/den)
 alpha=s.factor(t*Z-PT/TT)
 v=s.factor(s.Rational(3,2)*(alpha-Z+sE))
 u=s.factor(sD-sC-Z-v/3)
 VR=s.factor(aa*(alpha-2*u-2*v))
 VS=s.factor(bb*(alpha+2*u-2*v))
 Vz=s.factor(z*Z)
 return {'R':VR,'S':VS,'z':Vz,'alpha':alpha,'u':u,'v':v}
LT=lift(PT=1)
LD=lift(sC=3*z/(4*aa),sD=2/(z*k))
def dR(f):return s.diff(f,R)+k*s.diff(f,k)/(6*R)
def dS(f):return s.diff(f,S)+k*s.diff(f,k)/(6*S)
def dz(f):return s.diff(f,z)
def action(V,f):return V['R']*dR(f)+V['S']*dS(f)+V['z']*dz(f)
def div(V):return dR(V['R'])+dS(V['S'])+dz(V['z'])-s.Rational(5,6)*(V['R']/R+V['S']/S)
cT=s.factor(-LT['alpha']-LT['u']+s.Rational(7,3)*LT['v'])
M=s.factor(div(LT)+cT)
print('M_T=',M,flush=True)
Cp=k/3-z*z*k*k/(16*aa)
Det=bb*aa*(Cp*TT-z*z/16)
h2=s.factor(Det/(bb*bb*Cp*Cp))
# surviving beta coefficient/h after both integrations by parts.
res=s.factor(-(action(LD,M)+M*div(LD)+M*action(LD,h2)/(2*h2)))
print('res at R=S=z=k=1',s.factor(res.subs({R:1,S:1,z:1,k:1})),flush=True)
print('res=',res,flush=True)
out={'variables':'R=r²,S=s²,k6=RS,mu∝R^(−5/6)S^(−5/6)dR dS dz',
     'normalization':'h=-A*rho/(lambda*Cp)=-kappa; the beta residual is g=-div_mu(h*M_T*VD)=+div_mu(kappa*M_T*VD)',
     'LT':{a:str(v)for a,v in LT.items()},'LDshear':{a:str(v)for a,v in LD.items()},'M_T':str(M),'h_squared':str(h2),
     'remaining_beta_coefficient_over_h':str(res),
     'remaining_beta_coefficient_over_h_at_1':str(res.subs({R:1,S:1,z:1,k:1})),
     'remaining_beta_coefficient_over_kappa_at_1':str(-res.subs({R:1,S:1,z:1,k:1})),
     'certificate':False}
Path(__file__).with_name('actual-ruling-adjoints.json').write_text(json.dumps(out,indent=2)+'\n')
