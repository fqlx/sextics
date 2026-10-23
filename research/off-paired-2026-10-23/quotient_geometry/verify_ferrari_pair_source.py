from pathlib import Path
import json
import sympy as s
m,S,R,T,q,u,e,f,t=s.symbols('m S R T q u e f tau')
A=m+S; D=3*m*m+4*S*m+S*S-4*R
N=-S*A**3+2*R*A**2+8*R**2
qSSnum=-D**2+A*(7*m+3*S)*D-2*m*A**2*(6*m+4*S)
checks={'pair_trace_second_S_derivative':s.expand(qSSnum+2*N)==0}
d=t-1/t;rho=t+1/t
qt=e*d/4;kt=e*rho/2;h=s.cancel(qt/kt)
St=u**3/h-qt**2
Dt=s.cancel(D.subs({m:qt**2,S:St,R:u**6}))
Ut=(h*s.diff(St+qt**2,t)+2*h*qt*s.diff(qt,t))/(3*u**2-h*f)
# E=u3-h*(g+fu+q2), so actual implicit tangent uses h'*(u3/h)+2h q q'.
Ut=(s.diff(h,t)*u**3/h+2*h*qt*s.diff(qt,t))/(3*u**2-h*f)
expected=h*Dt/(2*t*u**3*(3*u**2-h*f))
checks['physical_tau_tangent']=s.cancel(Ut-expected)==0
checks['conic_parameter']=s.cancel(kt**2-4*qt**2-e**2)==0
# Constant reconstruction with trace sum zero.
r1,r2,r3,r4=s.symbols('r1 r2 r3 r4')
checks['constant_pair_reconstruction']=s.expand(((r1+r2)+(r1+r3)+(r1+r4))/2-r1-(r1+r2+r3+r4)/2)==0
out={'checks':checks,'status':'Exact pair trace, constant full-source reconstruction and actual tau tangent; no primitive.'}
assert all(checks.values()),checks
Path(__file__).with_name('ferrari-pair-source-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
