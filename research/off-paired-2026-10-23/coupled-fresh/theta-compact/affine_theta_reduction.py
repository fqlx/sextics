#!/usr/bin/env python3
"""Exact generic polynomial/J reduction of actual Theta moment on canonical curve."""
import json
from functools import lru_cache
from pathlib import Path
import sympy as s

a,b,q,c,d,e=s.symbols('a b q c d e')
pars=(c,d,e)
@lru_cache(None)
def redword(A,B,Q):
    if A and B:
        k=min(A,B)
        return redword(A-k,B-k,Q+3*k)
    if A>=2:
        return s.expand(-redword(A-2,B+2,Q)-c*redword(A-2,B,Q+2)-d*redword(A-1,B,Q+1)-e*redword(A-2,B,Q+1)-redword(A-2,B,Q))
    if B>=3:
        return s.expand(-redword(A+1,B-3,Q+3)-c*redword(A,B-2,Q+2)-d*redword(A,B-3,Q+4)-e*redword(A,B-2,Q+1)-redword(A,B-2,Q))
    return a**A*b**B*q**Q

def red(f):
    p=s.Poly(s.expand(f),a,b,q)
    return s.expand(sum(v*redword(*k) for k,v in p.terms()))

J=red(2*a*a+d*a*q-2*b*b)
da=red(-a*(2*c*q+d*a+e)-6*b*q*q)
db=red(b*(2*c*q+d*a+e)+3*q*q*(2*a+d*q))
def delta(f):
    return red(s.diff(f,q)*J+s.diff(f,a)*da+s.diff(f,b)*db)

def words(bound):
    return [(A,B,Q) for A,B in [(0,0),(1,0),(0,1),(0,2)] for Q in range((bound-3*A-3*B)//2+1)]

def mono(w):return a**w[0]*b**w[1]*q**w[2]

def vector(f,rows):
    pp=s.Poly(red(f),a,b,q)
    extra=set(pp.monoms())-set(rows)
    if extra:raise ValueError(extra)
    return s.Matrix([pp.coeff_monomial(mono(w)) for w in rows])

def main():
    rows=words(11)
    primitive=[mono(w) for w in words(7) if w!=(0,0,0)]
    basis=[1,q,q*q,q**3,q**4,a,a*q,b,b*q]
    cols=[delta(f) for f in primitive]+basis
    mat=s.Matrix.hstack(*(vector(f,rows) for f in cols))
    print('matrix',mat.shape,flush=True)
    determinant=s.factor(mat.det(method='domain-ge'))
    print('determinant',determinant,flush=True)
    Cp=c-d*d/4
    kappa=d*(Cp**3+8)/16
    Ntheta=red(2*c*b**3+4*d*b*b*q*q+6*b*q**4+e*a*q*q+e*d*q**3/2+kappa*q*q)
    sol=mat.inv()*vector(Ntheta,rows)
    sol=[s.factor(x) for x in sol]
    primitives=s.expand(sum(f*x for f,x in zip(primitive,sol)))
    coeff=sol[len(primitive):]
    check=red(Ntheta-delta(primitives)-sum(f*x for f,x in zip(basis,coeff)))
    assert check==0,check
    # Exact finite pole removal identity: Theta+e*zeta/2+d_q(b^3/(3q))
    # written after multiplication by J.
    F=b**3/(3*q)
    numerator=red(e*b*J/2+delta(b**3)/3)
    assert s.cancel(numerator/q-(Ntheta-kappa*q*q))==0
    result={
      'status':'Exact generic source-preserving affine Theta reduction, not a certificate',
      'curve':{'ab':'q^3','Q':'a^2+b^2+c*q^2+d*a*q+e*q+1','J':str(J)},
      'derivation':{'q':str(J),'a':str(da),'b':str(db)},
      'basis':[str(f) for f in basis],
      'coefficient_ring':'Q[c,d,e]',
      'numerator_words':[str(mono(w)) for w in rows],
      'exact_primitives':[str(f) for f in primitive],
      'matrix_determinant':str(determinant),
      'kappa':str(s.factor(kappa)),
      'theta_basis_coefficients':[str(x) for x in coeff],
      'theta_exact_primitive':str(s.factor(primitives)),
      'checks':{'matrix_invertible_generically':determinant!=0,'literal_polynomial_J_identity':True,'full_generic_reduction_identity':check==0},
    }
    out=Path(__file__).with_name('affine-theta-reduction-results.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('coefficients',list(zip(basis,coeff)),flush=True)
    print('primitive',s.factor(primitives),flush=True)
    print('saved',out,flush=True)
if __name__=='__main__':main()
