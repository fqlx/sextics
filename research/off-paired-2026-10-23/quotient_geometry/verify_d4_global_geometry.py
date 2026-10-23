from pathlib import Path
from itertools import combinations
from math import gcd
from functools import reduce
import json
import sympy as s
r,t,l,v,w=s.symbols('r t lambda v w')
X0=r*l;X1=l;X2=t*l;Y0=-t;Y1=v;Y2=r**3
D4=X1**2*X2*Y2+X0**3*Y0
F=sum(x**6 for x in [X0,X1,X2,Y0,Y1,Y2])+X0**3*X1*Y0*Y1/2+X1**3*X2*Y1*Y2/2+X0**2*X1*X2*Y0*Y2/3
expected=v**6+l**6+r**6*l**6+t**6*l**6+t**6+r**18-r**5*t**2*l**4/3
checks={'support_pullback':s.expand(D4)==0,'sextic_pullback':s.expand(F-expected)==0}
VV=[s.Matrix(x) for x in [(0,0,6),(6,0,6),(0,6,6),(0,6,0),(18,0,0)]]
interior=s.Matrix([5,2,4]);facets=set();strict=[]
for ids in combinations(range(5),3):
 a,b,c=[VV[i] for i in ids];n=(b-a).cross(c-a)
 if not any(n):continue
 vals=[n.dot(x-a) for x in VV]
 if all(x>=0 for x in vals) or all(x<=0 for x in vals):
  face=tuple(i for i,x in enumerate(vals) if x==0)
  if face in facets:continue
  facets.add(face);ip=n.dot(interior-a)
  strict.append(ip!=0 and (all(x>=0 for x in vals) and ip>0 or all(x<=0 for x in vals) and ip<0))
checks['base_facets_simplicial']=len(facets)==6 and all(len(x)==3 for x in facets)
checks['mixed_exponent_strict_interior']=all(strict)
checks['base_dimension_three']=s.Matrix.hstack(*[x-VV[0] for x in VV[1:]]).rank()==3
AA,BB,CC,DD,EE,MM=s.symbols('A B C D E M')
critical=[AA+BB+CC+DD+EE-MM,6*BB+18*EE-5*MM,6*CC+6*DD-2*MM,6*AA+6*BB+6*CC-4*MM]
sub={AA:MM*(2*w-s.Rational(1,6)),BB:MM*(-3*w+s.Rational(5,6)),CC:MM*w,DD:MM*(s.Rational(1,3)-w),EE:MM*w}
checks['critical_linear_relations']=all(s.expand(x.subs(sub))==0 for x in critical)
a=2*w-s.Rational(1,6);b=-3*w+s.Rational(5,6);d=s.Rational(1,3)-w
P=s.together(b**3*d-a*a*w*w).as_numer_denom()[0]
Q=s.together(b**5*d*d-729*a).as_numer_denom()[0]
checks['critical_polynomials_coprime']=s.gcd(P,Q)==1
out={'checks':checks,'facets':[list(x) for x in sorted(facets)],'critical_P':str(s.expand(P)),'critical_Q':str(s.expand(Q)),'status':'Exact nondegenerate full-dimensional toric model; global H20 vanishing follows from the stated toric/Serre/Kawamata--Viehweg argument. No certificate.'}
assert all(checks.values()),checks
Path(__file__).with_name('d4-global-geometry-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
