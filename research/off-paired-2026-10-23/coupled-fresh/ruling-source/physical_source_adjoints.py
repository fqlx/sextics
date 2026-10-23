"""Exact source-bearing T/S and E/W ruling-current adjoints.

This is constructive bookkeeping, not a nonexistence test. The final finite
residue coefficient has to vanish, or be cancelled, for a current to solve the
immutable source. Infinity companions are specified in the accompanying note.
"""
import json
from pathlib import Path
import sympy as s

R,S,z,k=s.symbols('R S z k',nonzero=True)
A=1+R; B=1+S; T=1+z**6
Cp=k/3-z*z*k*k/(16*A)
delta=3*R*S*z**6-3*R*S-8*R*z**6+R-S*z**6+2*S

def lift(PT=0,sC=0,sD=0,sE=0):
    """Lift a coefficient direction; sC,sD,sE are relative variations."""
    ca=2-1/R-3/S; cz=-6+4/R+2/S; t=6*z**6/T
    const=sC*(2*(1+1/R)-2*(1+1/S)-6)+sD*(-2*(1+1/R)+2*(1+1/S))+sE*(-2*(1+1/R)-4*(1+1/S)+12)
    Z=s.factor((ca*PT/T-const)/(ca*t+cz))
    alpha=s.factor(t*Z-PT/T)
    v=s.factor(s.Rational(3,2)*(alpha-Z+sE))
    u=s.factor(sD-sC-Z-v/3)
    return {'R':s.factor(A*(alpha-2*u-2*v)),
            'S':s.factor(B*(alpha+2*u-2*v)), 'z':s.factor(z*Z),
            'alpha':alpha,'u':u,'v':v}

def dR(f):return s.diff(f,R)+k*s.diff(f,k)/(6*R)
def dS(f):return s.diff(f,S)+k*s.diff(f,k)/(6*S)
def action(V,f):return V['R']*dR(f)+V['S']*dS(f)+V['z']*s.diff(f,z)
def div(V):return dR(V['R'])+dS(V['S'])+s.diff(V['z'],z)-s.Rational(5,6)*(V['R']/R+V['S']/S)
def char(V,q_power=0):return -V['alpha']-V['u']+s.Rational(5+2*q_power,3)*V['v']

LT=lift(PT=1)
LS=lift(sC=3*z/(4*A),sD=2/(z*k))
LE=lift(sE=2/z)
LW=lift(PT=z/(4*Cp),sE=2/z)
hT=s.factor(div(LT)+char(LT,1))
hE=s.factor(div(LE)+char(LE))
kappa2=s.factor(A*(T-z*z/(16*Cp))/(B*Cp))
m=s.factor(4*Cp/(z*k))  # kappa_E/kappa_S=2Cp/D.

def weighted_div(V,f):
    """div_mu(kappa f V)/kappa, without adjoining square roots."""
    return action(V,f)+f*div(V)+f*action(V,kappa2)/(2*kappa2)

def finite_residual(weight):
    """T/S weight f; E/W weight 1-f, modulo fiber exact and total d."""
    hTf=action(LT,weight)+hT*weight
    hEf=-action(LE,weight)+hE*(1-weight)
    return weighted_div(LS,hTf)-weighted_div(LW,m*hEf)

def at_point(f,values=None):
    return s.factor(f.subs(values or {R:1,S:1,z:1,k:1}))

if __name__=='__main__':
    # Factor each residue once; the explicit form remains in the JSON artifact.
    gT=s.factor(weighted_div(LS,hT))
    print('T/S finite residual / kappa at 1:',at_point(gT),flush=True)
    gE=s.factor(-weighted_div(LW,m*hE))
    print('E/W finite residual / kappa at 1:',at_point(gE),flush=True)
    out={'status':'UNSOLVED','coordinates':'R=r²,S=s²,k⁶=RS',
         'volume':'mu proportional R^(−5/6)S^(−5/6)dR dS dz',
         'T_lift':{a:str(v) for a,v in LT.items()},
         'shear_lift':{a:str(v) for a,v in LS.items()},
         'E_lift':{a:str(v) for a,v in LE.items()},
         'W_lift':{a:str(v) for a,v in LW.items()},
         'hT':str(hT),'hE':str(hE),'kappa_squared':str(kappa2),
         'kappa_E_over_kappa_S':str(m),
         'gT_over_kappa':str(gT),'gE_over_kappa':str(gE),
         'gT_at_1':str(at_point(gT)),'gE_at_1':str(at_point(gE)),
         'weighted_formula':'G[f]/kappa=D_S(V_T f+hT f)−D_W(m(−V_E f+hE(1−f))), D_V h=div_mu(kappa h V)/kappa'}
    Path(__file__).with_name('physical-source-adjoints.json').write_text(json.dumps(out,indent=2)+'\n')
