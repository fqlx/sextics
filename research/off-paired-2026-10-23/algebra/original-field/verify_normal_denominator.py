#!/usr/bin/env python3
"""Exact immutable normal/weight binding for eventual ambient certificate export."""
import json,hashlib,re
from pathlib import Path
import sympy as s

names='X0 X1 X2 Y0 Y1 Y2'.split()
xx=s.symbols(' '.join(names));env=dict(zip(names,xx))
source=Path('/workspace/off-paired-sextics/data/off-paired/instance.rec')
line=re.search(r'^F: (.*)$',source.read_text(),re.M).group(1)
F=s.sympify(line,locals=env)
X0,X1,X2,Y0,Y1,Y2=xx
weights=(0,1,1,-1,0,-1)
def G(f):return s.expand(sum(w*x*s.diff(f,x) for w,x in zip(weights,xx)))
J=2*(X1**6+X2**6-Y0**6-Y2**6)+X1**3*X2*Y1*Y2/2
checks={}
def ck(n,x):
    assert s.expand(x)==0,(n,x)
    checks[n]=True
ck('normal_denominator_binding',G(F)-3*J)
components={}
for m,coeff in s.Poly(F,*xx).terms():
    wt=sum(a*b for a,b in zip(m,weights))
    mon=coeff*s.prod(x**a for x,a in zip(xx,m))
    components[wt]=components.get(wt,0)+mon
ck('positive_extreme_weight',components[6]-X1**6-X2**6)
ck('negative_extreme_weight',components[-6]-Y0**6-Y2**6)

# Strict diagonal gradient dominance: choose a maximum-modulus coordinate.
mixed=F-sum(x**6 for x in xx)
bounds=[]
for x in xx:
    bounds.append(sum(abs(c) for m,c in s.Poly(s.diff(mixed,x),*xx).terms()))
assert all(b<6 for b in bounds)
checks['all_six_gradient_rows_strictly_dominant']=True

# Squarefreeness over the fraction field in the other coordinates follows
# from a nonzero monic resultant; this specialization is sufficient.
special=s.expand(F.subs({X0:1,X1:0,X2:0,Y0:0,Y2:0}))
ck('monic_separability_specialization',special-(Y1**6+1))
res=s.resultant(special,s.diff(special,Y1),Y1)
assert res!=0
checks['separability_resultant_nonzero']=True

out={'status':'Auxiliary denominator facts; no certificate asserted',
 'variable_order':names,'source_instance_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'G_weights':list(weights),'J':str(J),
 'weight_components':{str(k):str(v) for k,v in sorted(components.items())},
 'mixed_gradient_bounds':[str(x) for x in bounds],
 'separability_resultant':str(res),'checks':checks,'count':len(checks),
 'mathematical_conclusions':[
  'Projective F is smooth: the pure derivative6*z_i^5 dominates at a maximum-modulus nonzero coordinate.',
  'F is squarefree: monic inY1 with nonzero generic resultant.',
  'gcd_C(F,J)=1: a common irreducible factor would be G-homogeneous and divide both extreme weight components.',
  'Every nonzero G-homogeneous polynomial D is relatively prime to F; factor homogeneity and the disjoint extreme components prove this.'
 ],
 'formal_status':'The factor-homogeneity/coprimality arguments are mathematical proofs in the accompanying note, not Lean kernel verification.'}
dest=Path(__file__).with_name('normal-denominator-results.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'pass':True,'output':str(dest)}))
