from pathlib import Path
import json
import sympy as s
p,H,C,Z=s.symbols('p H C Z')
i=s.I
f=(H+C*p)**2-4*p**6
S=H+C*p
r=(S+Z)/2
v=(Z+2*i*p**3)/S
checks={}
def reduce_zero(expr):
    num,den=s.fraction(s.cancel(expr))
    return s.rem(num,Z**2-f,Z).expand()==0
for t in (p,H,C):
    Zt=s.diff(f,t)/(2*Z)
    dlogr=(s.diff(r,t)+s.diff(r,Z)*Zt)/r-(3/p if t==p else 0)
    expected={'p':-(2*C+3*H/p)/Z,'H':1/Z,'C':p/Z}[str(t)]
    checks['finite_torsion_log_'+str(t)]=reduce_zero(dlogr-expected)
    dlogv=(s.diff(v,t)+s.diff(v,Z)*Zt)/v/(2*i)
    expected2={'p':p**2*(3*H+2*C*p)/(S*Z),'H':-p**3/(S*Z),'C':-p**4/(S*Z)}[str(t)]
    checks['infinity_moving_log_'+str(t)]=reduce_zero(dlogv-expected2)
a,b=s.symbols('a b')
F=a**6+b**6+C*a*b+H
checks['physical_pullback']=s.expand(a*s.diff(F,a)-b*s.diff(F,b)+6*(b**6-a**6))==0
checks['C0_relative_log']=s.simplify((p**2*(3*H+2*C*p)/(S*Z)-3*p**2/Z).subs(C,0))==0
assert all(checks.values()), checks
out={'checks':checks,'status':'Exact symbolic interface identities only; no primitive or certificate.'}
Path(__file__).with_name('third-kind-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
