import sympy as s,json
from pathlib import Path
p,H,C=s.symbols('p H C');f=(H+C*p)**2-4*p**6;bs=[0,1,3,4]
unknowns=s.symbols('m0:4')+s.symbols('r0:6');R=sum(unknowns[4+i]*p**i for i in range(6))
E=sum(unknowns[i]*p**k*f for i,k in enumerate(bs))+s.diff(R,p)*f-R*s.diff(f,p)/2
matrix,_=s.linear_eq_to_matrix(s.Poly(E,p).all_coeffs(),unknowns)
out={'basis':bs,'new_basis_index':2,'meaning':'third-kind at infinity, residues constant; derivatives are compact','columns':{},'primitives':{}}
for v in [H,C]:
 target=-p**2*s.diff(f,v)/2
 rhs=s.Matrix([s.Poly(target,p).coeff_monomial(p**i)for i in range(10,-1,-1)])
 vec=[s.factor(a)for a in list(s.linsolve((matrix,rhs),unknowns))[0]]
 assert s.cancel((E-target).subs(dict(zip(unknowns,vec))))==0
 out['columns'][str(v)]=[str(a)for a in vec[:4]];out['primitives'][str(v)]=[str(a)for a in vec[4:]]
 print(v,vec[:4],flush=True)
Path(__file__).with_name('third-kind-connection.json').write_text(json.dumps(out,indent=2))
