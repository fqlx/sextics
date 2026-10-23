import sympy as s
import json
from pathlib import Path
p,H,C=s.symbols('p H C')
f=(H+C*p)**2-4*p**6
basis=[0,1,3,4]
unknowns=s.symbols('m0:4')+s.symbols('r0:6')
r=sum(unknowns[4+i]*p**i for i in range(6))
base=sum(unknowns[i]*p**k*f for i,k in enumerate(basis))+s.diff(r,p)*f-r*s.diff(f,p)/2
matrix,zero=s.linear_eq_to_matrix(s.Poly(base,p).all_coeffs(),unknowns)
out={'basis':basis,'f':str(f),'convention':'derivative basis columns; d(R/Z) exact'}
for v in [H,C]:
    columns=[]; primitives=[]
    for j in basis:
        target=-p**j*s.diff(f,v)/2
        rhs=s.Matrix([s.Poly(target,p).coeff_monomial(p**i)for i in range(10,-1,-1)])
        sol=matrix.inv_quick()*rhs if False else s.linsolve((matrix,rhs),unknowns)
        vec=list(sol)[0]
        assert len(vec)==10
        vec=[s.factor(x)for x in vec]
        assert s.cancel((base-target).subs(dict(zip(unknowns,vec))))==0
        columns.append(vec[:4]); primitives.append(vec[4:])
        print(v,j,vec[:4],flush=True)
    out[str(v)]={'columns':[[str(x)for x in col]for col in columns],'primitives':[[str(x)for x in col]for col in primitives]}
Path(__file__).with_name('reconstructed-connection.json').write_text(json.dumps(out,indent=2))
