"""Exact check of the simplest mixed logarithmic current. No primitive claim.
Prepared for fqlx with OpenAI ChatGPT assistance.
"""
import json
from pathlib import Path
import sympy as s

y,p,b,T,I,J=s.symbols('y p b T I J')
H=(1+y**6)*p**3+y*p**2/2+I*y*p/2+J
P=I**6*T**4+b**9*T**2+(I*b**8/2-J*b**9)*T+b**12+b**9
K=s.diff(H,p);Q=s.diff(P,T)
def D(g,x):
 return s.diff(g,x)-s.diff(g,p)*s.diff(H,x)/K-s.diff(g,T)*s.diff(P,x)/Q
N=y**3*p**2/K
thetaI=-s.diff(P,I)/(2*b**2*T*Q)
thetaJ=b**7/(2*Q)
assert s.cancel(D(thetaI,J)-D(thetaJ,I))==0
assert s.cancel(D(N,J)+y**4*p*(p+I)/K**3)==0
assert s.cancel(D(N,I)+y**4*p**2*(3*(1+y**6)*p**2+2*y*p+3*I*y/2)/(2*K**3))==0
O=D(N,J)*thetaI-D(N,I)*thetaJ
point={I:s.Integer(1),J:s.Integer(2),y:s.Integer(1),p:s.Integer(-1),b:s.Integer(1)}
assert H.subs(point)==0
Ps=P.subs(point);Qs=Q.subs(point)
assert s.cancel(O.subs(point)-1/(121*Qs))==0
resultant=s.resultant(Ps,Qs,T)
assert resultant==s.Rational(33125,16)
report={'scope':'The current dlog(b-y^2) wedge (N dy) wedge totalTheta has a nonzero simple-pole residue. This does not exclude other currents and is not a protected primitive.',
 'H':str(H),'P':str(P),'N':str(N),'theta_I':str(thetaI),'theta_J':str(thetaJ),
 'checks':['commuting parameter components of totalTheta','implicit derivatives of N','valid point of H=0 and f=0','nonzero residue O=1/(121 Q)','P and Q relatively prime at that point'],
 'specialized_P':str(Ps),'specialized_Q':str(Qs),'resultant':str(resultant),'all_exact_checks':True}
Path(__file__).with_name('receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
