from pathlib import Path
import json
import sympy as s
p,L,C,k,Z,V=s.symbols('p L C s Z V')
S=L+C*(p-k)
f=S**2-4*p**6
eta=V/((p-k)*Z)
etaC=s.diff(eta,C)+s.diff(eta,Z)*s.diff(f,C)/(2*Z)
checks={'exact_endpoint_source_direction':s.cancel(etaC+V*S/Z**3)==0}
x,y,z=s.symbols('x y z')
H=1+x**6+y**6+z**6+x*y*z/2
Cphys=x**3*z/2+x*y/3
sphys=-3*z/2
Lphys=s.expand(H+sphys*Cphys)
checks['physical_adapted_L']=s.expand(Lphys-(1+x**6+y**6+z**6-s.Rational(3,4)*x**3*z**2))==0
J=s.diff(Lphys,x)*s.diff(Cphys,y)-s.diff(Lphys,y)*s.diff(Cphys,x)
phi=y**3/J
dCdx=s.diff(Cphys,x)-s.diff(Cphys,y)*s.diff(Lphys,x)/s.diff(Lphys,y)
checks['oriented_physical_coefficient']=s.cancel(phi*dCdx+1/(6*y**2))==0
assert all(checks.values()),checks
out={'checks':checks,'status':'Exact movingpole source-direction and actual coefficient; phi_C residue correction remains open.'}
Path(__file__).with_name('moving-pole-kernel-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
