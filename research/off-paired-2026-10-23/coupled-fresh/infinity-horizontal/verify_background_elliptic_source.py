"""Actual physical background elliptic factors and source differential."""
import sympy as s,json
from pathlib import Path
x,y,z,H,a,q=s.symbols('x y z H a q',nonzero=True)
Hxy=1+x**6+y**6+z**6+x*y*z/2
Cxy=x**3*z/2+x*y/3
ss=x**3+y**3;dd=x**3-y**3
checks=[]
checks.append(s.expand(ss**2-(2*(x*y)**3-z*x*y/2-(1+z**6-Hxy)))==0)
checks.append(s.expand(dd**2-(-2*(x*y)**3-z*x*y/2-(1+z**6-Hxy)))==0)
checks.append(s.expand(Cxy-(x*y/3+z*(ss+dd)/4))==0)
JHq=s.diff(Hxy,x)*x-s.diff(Hxy,y)*y
checks.append(s.expand(JHq-6*ss*dd)==0)
checks.append(s.cancel(y**3/JHq-(1/dd-1/ss)/12)==0)
Q=3*s.symbols('C')-s.Rational(3,2)*a*z
C=s.symbols('C');P=a**4+Q**6+a*a*(z**6+Q*z/2+1-H)
PaC=s.diff(P,a)
Paq=4*a**3+2*a*(z**6+q*z/2+1-H)
Pq=6*q**5+a*a*z/2
checks.append(s.cancel(PaC.subs(C,q/3+a*z/2)-(Paq-s.Rational(3,2)*z*Pq))==0)
checks.append(s.cancel((s.Rational(1,3)-z*Pq/(2*Paq))-PaC.subs(C,q/3+a*z/2)/(3*Paq))==0)
b=q**3/a;S=a+b;D=a-b;w=2*a*a+(1+z**6-H+z*q/2)
# Identities on P=0, with K=−a²−q⁶/a².
K=-a*a-q**6/a**2
w0=2*a*a+K
checks.append(s.cancel(S*D-w0)==0)
checks.append(s.cancel(q**3/(3*Paq)-(1/D-1/S)/12).subs(H,1+z**6+z*q/2+a*a+q**6/a**2).cancel()==0)
assert all(checks),checks
out={'checks':len(checks),'passed':True,'actual_source':'y³ dx∧dy=(1/d−1/s) dH∧dq/12','certificate':False}
Path(__file__).with_name('background-elliptic-source-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
