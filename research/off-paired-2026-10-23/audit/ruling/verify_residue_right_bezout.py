"""Independent symbolic-function audit of the actual residue RIGHT inverse."""
import hashlib
import json
from pathlib import Path
import sympy as s

root=Path(__file__).resolve().parents[2]
source=root/'coupled-fresh/genus4-gm-independent/residue-ore-bezout-results.json'
data=json.loads(source.read_text())
u=s.symbols('u')
f=s.Function('f')(u)
U=[s.sympify(t,locals={'u':u}) for t in data['U_low_to_high']]
V=[s.sympify(t,locals={'u':u}) for t in data['V_low_to_high']]
def apply(coefficients,g):
    return sum(c*s.diff(g,u,n) for n,c in enumerate(coefficients))
def theta(g):
    return u*s.diff(g,u)
def left_one(g):
    h=u*(4-u)*s.diff(g,u,2)+3*(2-u)*s.diff(g,u)
    return 2*(theta(h)+h)
def left_two(g):
    h=g-theta(g)
    h=h-2*theta(h)
    return -4*theta(h)

# This computes L1(Uf)+L2(Vf), not U(L1f)+V(L2f).
expr=s.expand(left_one(apply(U,f))+left_two(apply(V,f))-f)
checks=[]
for n in range(6):
    derivative=f if n==0 else s.diff(f,u,n)
    coefficient=expr.coeff(derivative)
    assert s.cancel(coefficient)==0,n
    checks.append('arbitrary_function_derivative_'+str(n))
assert s.expand(expr-sum(expr.coeff(f if n==0 else s.diff(f,u,n))
                       *(f if n==0 else s.diff(f,u,n)) for n in range(6)))==0
out={'status':'passed','checks':checks,'count':len(checks),
     'arithmetic':'exact symbolic arbitrary-function Leibniz expansion, independently generated L1 and L2',
     'identity':'L1 U+L2 V=1 (RIGHT inverse)',
     'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
     'scope':'Exact source-residue inverse only; rational lifting, other poles and full (Z-1) source remain unsolved.',
     'certificate':False}
Path(__file__).with_name('residue-right-bezout-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
