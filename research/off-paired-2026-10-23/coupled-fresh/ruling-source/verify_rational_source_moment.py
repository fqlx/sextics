"""Exact rationalization and inverse-root moment of the physical source."""
import json
from pathlib import Path
import sympy as s
i,J,z=s.symbols('i J z',nonzero=True)
T=1+z**6
k=3*i*z**2/(4*T)
A=k*k*T/J
R=A-1
S=k**6/R
B=1+S
Delta=3*R*S*z**6-3*R*S-8*R*z**6+R-S*z**6+2*S
v=z**6/(64*T**4*A*B)
h=z**4*A/(8*k*T*T*Delta)
N=9*i*i*z**4-16*J*T
M=256*T**5*N+729*i**6*J*z**12
checks=[]
def check(name,expr):
    assert s.factor(expr)==0,name
    checks.append(name)
check('inverse_physical_norm',R*S-k**6)
check('source_h_simplification',h-3*i*z**6/(32*J*T*T*Delta))
check('inverse_root_equation',v-64*J*z**2*T*T*N/(9*i*i*M))
check('source_first_moment',h*s.diff(v,z)/v-768*i*z**5*T**3/M)
check('source_second_moment',h*s.diff(v,z)/v**2-108*i**3*z**3*T/(J*N))
check('w_equals_z_squared_moment',h*s.diff(v,z)/(2*z*v*v)-54*i**3*z*z*T/(J*N))
out={'status':'passed','checks':checks,'count':len(checks),
     'scope':'Exact actual scalar source/root-moment identities. Full curve kernel and adjoint source match remain necessary; no certificate.',
     'certificate':False}
Path(__file__).with_name('rational-source-moment-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
