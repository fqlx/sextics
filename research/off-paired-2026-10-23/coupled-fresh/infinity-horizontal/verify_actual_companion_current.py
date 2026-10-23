"""Actual rational B lift and literal fiber corrections for the xi2 source."""
import json
from pathlib import Path
import sympy as s
R,S,z,k=s.symbols('R S z k',nonzero=True)
Ap=1+R;Bp=1+S;Cp=k/3;Dp=z*k/2;Ep=z/2;Tp=1+z**6
tt=6*z**6/Tp
ca=2-1/R-3/S;cz=-6+4/R+2/S
Z=s.factor(-1/(S*(ca*tt+cz)))
alpha=s.factor(tt*Z)
v=s.factor(s.Rational(3,2)*(alpha-Z))
u=s.factor(-Z-v/3)
VB={'R':s.factor(Ap*(alpha-2*u-2*v)),
    'S':s.factor(Bp*(alpha+2*u-2*v)+1),
    'z':s.factor(z*Z),'alpha':alpha,'u':u,'v':v}
def dR(f):return s.diff(f,R)+k*s.diff(f,k)/(6*R)
def dS(f):return s.diff(f,S)+k*s.diff(f,k)/(6*S)
def act(f):return VB['R']*dR(f)+VB['S']*dS(f)+VB['z']*s.diff(f,z)
checks={}
for name,co,w1,w2,target in [('A',Ap,2,2,0),('B',Bp,-2,2,1),
 ('C',Cp,0,s.Rational(4,3),0),('D',Dp,1,s.Rational(5,3),0),
 ('E',Ep,0,s.Rational(2,3),0),('T',Tp,0,0,0)]:
    checks['physical_B_'+name]=s.factor(act(co)+(w1*u+w2*v-alpha)*co-target)==0

# Independent literal Cartan/homogeneity checks on the generic canonical curve.
A,B,C,D,E,T,a,b,q=s.symbols('A B C D E T a b q',nonzero=True)
Q=A*a*a+B*b*b+C*q*q+D*a*q+E*q+T
Qa=s.diff(Q,a);Qb=s.diff(Q,b);Qq=s.diff(Q,q);J=a*Qa-b*Qb
aq=(-a*Qq-3*q*q*Qb)/J;bq=(b*Qq+3*q*q*Qa)/J
def dq(f):return s.diff(f,q)+aq*s.diff(f,a)+bq*s.diff(f,b)
def par(f,p):
    P=s.diff(Q,p)
    return s.diff(f,p)-a*P*s.diff(f,a)/J+b*P*s.diff(f,b)/J
def H1(f):return 2*A*par(f,A)-2*B*par(f,B)+D*par(f,D)
def H2(f):return 2*A*par(f,A)+2*B*par(f,B)+s.Rational(4,3)*C*par(f,C)+s.Rational(5,3)*D*par(f,D)+s.Rational(2,3)*E*par(f,E)
def HQ(f):return sum(p*par(f,p)for p in (A,B,C,D,E,T))
def zero_curve(expr):
    nn=s.together(expr).as_numer_denom()[0]
    return s.factor(nn.subs(b,q**3/a).subs(T,-A*a*a-B*q**6/a**2-C*q*q-D*a*q-E*q))==0
eta=b/J;xi2=1/b
checks['H1_eta_literal']=zero_curve(H1(eta)-eta)
checks['H2_eta_Cartan']=zero_curve(H2(eta)+s.Rational(5,3)*eta-s.Rational(2,3)*dq(q*eta))
checks['H1_xi2_literal']=zero_curve(H1(xi2)+xi2)
checks['H2_xi2_Cartan']=zero_curve(H2(xi2)-xi2/3-s.Rational(2,3)*dq(q*xi2))
checks['Q_scale_eta']=zero_curve(HQ(eta)+eta)
checks['Q_scale_xi2']=zero_curve(HQ(xi2))
assert all(checks.values()),checks
out={'checks':checks,'passed':True,
 'VB':{name:str(value)for name,value in VB.items()},
 'c2':'u_B-v_B/3',
 'literal_B_connection':'nabla_VB xi2=nabla_B xi2+c2*xi2-(2*v_B/3)*d_q(q/b)',
 'density':'mu=dR*dS*dz/(108*k^5),k^6=R*S',
 'ME':'div_mu(VE)+c_eta,E; use actual outer-E lift',
 'remaining_xi2':'G2=div_mu(ME*VB)+ME*c2',
 'partial_current':'Jpartial=eta_b wedge i_VE(mu)+ME*xi2 wedge i_VB(mu)+K*mu, K=-(2/3)*(v_E*q*b/J+ME*v_B*q/b)',
 'source_identity':'(-nabla_E eta_b) wedge mu=d_total Jpartial+G2*xi2 wedge mu',
 'orientation':'relative dq before base mu',
 'certificate':False}
Path(__file__).with_name('actual-companion-current.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({key:value for key,value in out.items()if key!='VB'}))
