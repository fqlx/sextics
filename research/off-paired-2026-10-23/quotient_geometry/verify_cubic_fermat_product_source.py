from pathlib import Path
import json
import sympy as s
al,be,xi,eta,nu,w=s.symbols('alpha beta xi eta nu varpi')
M=s.Matrix([[xi/(6*al**5),0,al,0],[eta/(6*al**5),0,-al*xi**5/eta**5,0],[0,nu/(6*be**5),0,be],[0,w/(6*be**5),0,-be*nu**5/w**5]])
det=s.factor(M.det())
volume=-al**-4*be**-4/(36*eta**5*w**5)
num=s.together(det-volume).as_numer_denom()[0]
rem=s.groebner([xi**6+eta**6-1,nu**6+w**6-1],xi,nu,eta,w).reduce(s.expand(num))[1]
x,a,u,v=s.symbols('x a u v')
B=x*u/2+x**3*a*u*v/2+x*a*v/3
Bnew=al*be*xi*nu/2+al**4*be**2*xi**3*eta*nu*w/2+al**2*be*xi*eta*w/3
checks={'full_volume_orientation':rem==0,'three_coupling_weights':s.expand(B.subs({x:al*xi,a:al*eta,u:be*nu,v:be*w})-Bnew)==0}
out={'checks':checks,'status':'Exact fixed-Fermat-product physical source normalization; no contraction.'}
assert all(checks.values()),checks
Path(__file__).with_name('cubic-fermat-product-source-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
