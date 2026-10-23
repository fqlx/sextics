#!/usr/bin/env python3
"""Exact generic projectors to accelerate the actual compact Taylor solve."""
import hashlib,json
from pathlib import Path
import sympy as s

base=Path('/workspace/off-paired-research-new')
path=base/'coupled-fresh/theta-compact/rank8-descended-connection-results.json'
data=json.loads(path.read_text())
i,j,v,n=s.symbols('i j v n')
def parse(x):return s.sympify(x.replace('^','**'),locals={'i':i,'j':j,'v':v})
den=parse(data['GammaV_denominator']).subs(v,0)
R=s.Matrix([[parse(x).subs(v,0)/(6*den) for x in row]
            for row in data['GammaV_numerator']])
E=s.eye(8)
roots=[s.Rational(1,6),s.Rational(1,3),s.Rational(2,3),s.Rational(5,6)]
def simp(M):return M.applyfunc(s.expand)
checks={}
def ck(name,M):
    assert simp(M)==s.zeros(8),(name,M)
    checks[name]=True
pol=E
for lam in roots:pol=simp(pol*(R-lam*E))
ck('semisimple_four_factor_minimal_polynomial',pol)
projectors=[]
for lam in roots:
    P=E
    for mu in roots:
        if mu!=lam:P=simp(P*(R-mu*E)/(lam-mu))
    ck('projector_eigenvalue_'+str(lam),R*P-lam*P)
    projectors.append(P)
ck('sum_of_projectors',sum(projectors,s.zeros(8))-E)

# For every integer n>=0 all denominators are nonzero, and
# (n I+R)^-1=sum P_lam/(n+lam). This is a universal recurrence formula,
# not evidence that the ensuing Taylor series is rational.
out={'status':'Exact generic Taylor-recursion interface; no source primitive asserted',
     'connection_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
     'roots':[str(x) for x in roots],
     'recurrence_inverse':'(nI+R0)^-1 = sum_lam projector_lam/(n+lam), n>=0',
     'projectors':[[[str(x) for x in row] for row in P.tolist()] for P in projectors],
     'checks':checks,'count':len(checks)}
dest=Path(__file__).with_name('zero-residue-projector-results.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'pass':all(checks.values()),'output':str(dest)}))
