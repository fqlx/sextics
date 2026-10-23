from pathlib import Path
import json
import sympy as s
x,y,z,a,b,u,v=s.symbols('x y z a b u v')
H=1+x**6+y**6+z**6+x*y*z/2
C=x**3*z/2+x*y/3
F=a**6+b**6+C*a*b+H
Hu=1+u**6/v**2+v**2+z**6+u*z/2
Cu=u**3*z/(2*v)+u/3
G=u**6+v**4+(1+z**6+a**6+b**6+u*z/2+u*a*b/3)*v**2+u**3*z*a*b*v/2
subs={u:x*y,v:y**3}
checks={
 'physical_source_jacobian':s.det(s.Matrix([x*y,y**3]).jacobian([x,y]))==3*y**3,
 'H_retained':s.cancel(Hu.subs(subs)-H)==0,
 'C_retained':s.cancel(Cu.subs(subs)-C)==0,
 'cleared_equation':s.expand(G.subs(subs)-y**6*F)==0,
 'physical_density':s.cancel((v**4/(3*G**2)).subs(subs)*3*y**3-y**3/F**2)==0,
}
assert all(checks.values()),checks
out={'checks':checks,'status':'Exact source-carrying coordinate identities only; no current or certificate.'}
Path(__file__).with_name('source-constant-quotient-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
