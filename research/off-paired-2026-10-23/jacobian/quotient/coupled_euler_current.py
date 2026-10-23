"""Exact physical/canonical audit; no existence claim for the missing D."""
import json
from pathlib import Path
import sympy as s

Z,h,u,v,k=s.symbols('Z h u v k')
xs=(Z,h,u,v)
H=1+Z**-2+h**6
C=Z**2+u**6+v**6
B=u/s.Integer(2)+h*v/3+h*u*v/(2*Z)
kap=B**3/(C*H**2)
K=2*C*h**6-H*v**6
L=2*(Z**2+u**6)*h**6+(1+Z**-2)*v**6
def E(q): return h*s.diff(q,h)-v*s.diff(q,v)
def ck(name,q):
    assert s.cancel(q)==0, name
    checks.append(name)
checks=[]
ck('E(B)=0',E(B))
ck('E(K)=6L',E(K)-6*L)
ck('E(log k)=-6K/(CH)',E(kap)/kap+6*K/(C*H))
ck('U(log k)=-1/(2CH)',E(kap)/(12*K*kap)+1/(2*C*H))
divU=s.diff(h/(12*K),h)-s.diff(v/(12*K),v)
ck('div U=-L/(2K^2)',divU+L/(2*K**2))
t=4*k+27
f=(27-2*k)/(2*t)
c=3*(27-23*k)/t**2
ck('P log derivative V coefficient',k*s.diff(f,k)+3/t-c)
ck('P log derivative W coefficient',-2*f+(27-2*k)/t)
# Set D(log k)=-div(U)/c and div D=0, retaining two components.
Dl=L/(2*K**2*c.subs(k,kap))
ck('full current V coefficient',divU+c.subs(k,kap)*Dl)
ck('full current W coefficient',-2*(-1/(2*C*H))-1/(C*H))
out={'status':'exact constructive reduction only; D not constructed',
     'checks':checks,'count':len(checks)}
Path(__file__).with_name('coupled-euler-current-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
