import json,sympy as s
from pathlib import Path
root=Path(__file__).parent
p=json.loads((root/'j1728_boundary_jet.json').read_text())
q,e=s.symbols('q ell');rel=e*e-e+1
R=s.sympify(p['rational_square_root_factor']);Rl=s.sympify(p['lambda_derivative_root_factor'])
F=s.sympify(p['boundary_F_over_r'])/(2*e);Fl=s.sympify(p['derivative_F_over_r'])/(2*e)
def zero_mod(expr):
 num=s.together(expr).as_numer_denom()[0]
 assert s.rem(s.Poly(num,e),s.Poly(rel,e)).is_zero
zero_mod(F-(e*R)**2)
zero_mod(Fl-2*(e*R)*(e*Rl))
branch=11664*(1+q**6)**4-q**6
assert s.degree(branch,q)==24 and s.gcd(branch,s.diff(branch,q))==1
out={'ell_relation':'ell²-ell+1=0','boundary_h':'q³/[54(1+q⁶)²]','intrinsic_twist':'w=s/v','w_cubed_over_r_root':str(e*R),'root_lambda_jet':str(e*Rl),'curve':'xi²=11664(1+q⁶)^4-q⁶','genus':11,'holomorphic_basis':'q^j dq/xi, j=0,...,10','verified':['w³/r=(ell R0)²','lambda(w³/r)=2ell² R0 R0_lambda','branch polynomial degree24 and squarefree'],'remaining':'These are boundary hol1 candidates. Extension to global odd hol1 on the intrinsic slope surface, and actual nonzero Gysin/source binding, remain unproved.'}
(root/'j0_boundary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
