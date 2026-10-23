#!/usr/bin/env python3
"""Independent Fraction arithmetic audit of selected saved matrix columns."""
import json, random, struct, sys
from pathlib import Path
sys.path.insert(0,'/workspace/off-paired-research-published')
from ansatz import F,A,Q,add,scl,mul,der,char

ROOT=Path(__file__).resolve().parent
p=int(sys.argv[1]) if len(sys.argv)>1 else 1000003
m=json.loads((ROOT/f'system-{p}.json').read_text())
D={tuple(e):Q(c) for e,c in m['D']}
assert {sum(e) for e in D}=={18}
assert all(char(e)==(0,0) for e in D)
assert all(sum(e)==42 and e[3]<12 and char(tuple(e))==(3,0) for e in m['row_exponents'])
assert m['F']==[[list(e),str(c)] for e,c in F.items()]
assert m['A']==[[list(e),str(c)] for e,c in A.items()]
ff=mul(F,F);lead=(0,0,0,12,0,0);assert ff[lead]==1
rest={e:c for e,c in ff.items() if e!=lead}
def rem(poly):
    out=dict(poly)
    while True:
        high=[e for e in out if e[3]>=12]
        if not high:return out
        e=max(high,key=lambda e:e[3]);c=out.pop(e)
        base=tuple(a-b for a,b in zip(e,lead))
        for f,d in rest.items():
            k=tuple(a+b for a,b in zip(base,f))
            out[k]=out.get(k,Q(0))-c*d
            if not out[k]:del out[k]

choose=set(random.Random(421).sample(range(m['columns']),12));checked=0
with (ROOT/f'system-{p}.bin').open('rb') as stream:
    header=struct.unpack('<4I',stream.read(16))
    assert header[:3]==(m['rows'],m['columns'],p)
    for j in range(m['columns']+1):
        n=struct.unpack('<I',stream.read(4))[0];data=stream.read(8*n)
        if j not in choose and j!=m['columns']:continue
        saved={tuple(m['row_exponents'][r]):c for r,c in struct.iter_unpack('<II',data)}
        if j<m['columns']:
            i,e=m['names'][j];N={tuple(e):Q(1)}
            col=add(scl(mul(D,mul(N,der(F,i))),-1),mul(F,add(mul(D,der(N,i)),scl(mul(N,der(D,i)),-1))))
        else:col=scl(mul(A,mul(D,D)),-1)
        expected={e:c.numerator*pow(c.denominator,-1,p)%p for e,c in rem(col).items() if c.numerator%p}
        assert expected==saved,(j,len(expected),len(saved))
        checked+=1
report={'prime':p,'checked_columns_including_rhs':checked,'status':'passed',
        'additional_checks':['original F/A binding','degree 18 of D','character zero of D',
                             'degree 42 of all rows','row character (3,0)','Y0 exponents below 12']}
(ROOT/f'audit-{p}.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
