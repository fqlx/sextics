#!/usr/bin/env python3
"""Literal D32 series at a^6=-1, v^6=-1 after the two corner blowups.

Keep zeta^6=-1 and q^6=1, with v0=q/zeta and
a=zeta*(1-br)^(1/6), v=v0*(1-nu)^(1/6), nu=v^6+1.
"""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import hashlib,json,pickle
import sympy as s
HERE=Path(__file__).resolve().parent
SOURCE=Path('/workspace/research/round9/abel_prym/effective_graph.pickle')
graph=pickle.loads(SOURCE.read_bytes())['D']
z,q=s.symbols('zeta q')
out=defaultdict(Fraction)
MAXWT=30
for ex,co in graph.items():
    ep=ex[0]+ex[1]-17
    for j in range(5):
        b=ex[4]+j-2
        wt=3*ep+6*b+6*j
        if wt>MAXWT:continue
        for k in range(3):
            cf=Fraction(int(co))*Fraction(s.binomial(s.Rational(ex[3],6),j))*Fraction(s.binomial(s.Rational(ex[1],6),k))*(-1)**(j+k)
            ze=ex[3]-ex[1]
            quo,rem=divmod(ze,6)
            cf*=Fraction(-1)**quo
            out[ep,b,j,k,rem,ex[1]%6]+=cf
out={key:val for key,val in out.items() if val}
assert all(key[1]>=0 for key in out),[key for key in out if key[1]<0]
by=defaultdict(lambda:0)
for (ep,b,r,nu,ze,qe),cf in out.items():
    by[ep,b,r,nu]+=s.Rational(cf.numerator,cf.denominator)*z**ze*q**qe
rows=[]
for key,cf in sorted(by.items(),key=lambda kv:(kv[0][3],3*kv[0][0]+6*kv[0][1]+6*kv[0][2],kv[0])):
    ep,b,r,nu=key
    rows.append({'eps':ep,'b':b,'r':r,'nu':nu,'old_weight':3*ep+6*b+6*r,'coefficient':str(s.factor(cf))})
report={'D_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
 'relations':'zeta^6=-1,q^6=1; a=zeta*(1-br)^(1/6),v=(q/zeta)*(1-nu)^(1/6)',
 'strict_graph':'D/(eps^17*b^2)', 'max_old_weight':MAXWT,'max_nu_exponent':2,'rows':rows,
 'scope':'Exact truncated formal series from original D; no local normal form claim.'}
(HERE/'special_P_series.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
