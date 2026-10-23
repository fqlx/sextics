#!/usr/bin/env python3
"""Construct the three CM graph certificate assembly with free physical sources.

Each degree-18 graph may carry any homogeneous degree-six source in the
24-dimensional target character. The three sources must add to the immutable A.
The polynomial quotient and radial gauges are exact, as in graph-denominator.
This is one explicit construction, not a denominator-power search.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import struct
import sys
import time

sys.path.insert(0, '/workspace/off-paired-research-published')
from ansatz import F as FQ, A as AQ, char, mons

ROOT = Path(__file__).resolve().parent
Y = 1 << 18
WEIGHTS = [(0,0),(2,0),(0,1),(1,0),(3,0),(3,5)]
def encode(e): return sum(v << (6*i) for i,v in enumerate(e))
def decode(k): return tuple((k >> (6*i)) & 63 for i in range(6))

def run(p,families):
    start = time.time()
    def cv(q): return q.numerator * pow(q.denominator, -1, p) % p
    F = {encode(e):cv(q) for e,q in FQ.items()}
    def add(a,b):
        out = dict(a)
        for k,c in b.items():
            v = (out.get(k,0)+c) % p
            if v: out[k] = v
            else: out.pop(k,None)
        return out
    def mul(a,b):
        out = defaultdict(int)
        for k,c in a.items():
            for l,d in b.items(): out[k+l] = (out[k+l]+c*d) % p
        return {k:c for k,c in out.items() if c}
    def scale(a,c): return {k:v*c%p for k,v in a.items() if v*c%p}
    def der(a,i):
        return {k-(1 << (6*i)):v*((k >> (6*i))&63)%p
                for k,v in a.items() if (k >> (6*i))&63}
    FF = mul(F,F)
    assert FF[12*Y] == 1
    FFrest = [(k,c,(k >> 18)&63) for k,c in FF.items() if k != 12*Y]
    def rem(poly):
        buckets = [{} for _ in range(43)]
        for k,c in poly.items(): buckets[(k >> 18)&63][k] = c
        for j in range(42,11,-1):
            for k,c in buckets[j].items():
                if not c: continue
                base = k-12*Y
                for l,v,ly in FFrest:
                    kk=base+l; b=buckets[j-12+ly]
                    b[kk] = (b.get(kk,0)-c*v)%p
            buckets[j].clear()
        return {k:c for b in buckets[:12] for k,c in b.items() if c}

    sources = [e for e in mons(6) if char(e)==(3,0)]
    assert len(sources)==24
    source_index = {encode(e):j for j,e in enumerate(sources)}
    X = [{6 << (6*i):1} for i in range(3)]
    HX = add(add(X[0],X[1]),X[2])
    FY = {6 << (6*i):1 for i in range(3,6)}
    col_specs = []
    for i in range(6):
        want = ((3+WEIGHTS[i][0])%6, WEIGHTS[i][1])
        for e in mons(19):
            if e[3]<6 and (i!=3 or e[3]==0) and char(e)==want:
                col_specs.append((i,e,encode(e)))
    columns=[]; names=[]; all_rows=set(); denominators=[]
    support_specs=[(block,held) for block in families for held in range(3)]
    for support,(block,held) in enumerate(support_specs):
        a,b = [i for i in range(3) if i!=held]
        powers=X if block=='X' else [{6 << (6*(i+3)):1} for i in range(3)]
        T=add(powers[a],powers[b]); K=mul(powers[a],powers[b])
        D=add(mul(FY,mul(T,T)),scale(mul(HX,K),16))
        denominators.append([[list(decode(k)),c] for k,c in D.items()])
        FD=mul(F,D); DD=mul(D,D)
        Pi=[scale(add(mul(D,der(F,i)),mul(F,der(D,i))),-1) for i in range(6)]
        for i,e,k in col_specs:
            col={k+l:v for l,v in Pi[i].items()}
            if e[i]:
                unit=1 << (6*i)
                for l,v in FD.items():
                    kk=k-unit+l; col[kk]=(col.get(kk,0)+e[i]*v)%p
            reduced={(support,k):c for k,c in rem(col).items()}
            if reduced:
                columns.append(reduced); names.append(['N',block,held,i,list(e)])
                all_rows.update(reduced)
        for j,e in enumerate(sources):
            reduced={(support,k):c for k,c in rem({encode(e)+k:v for k,v in DD.items()}).items()}
            reduced[(len(support_specs),j)]=1
            columns.append(reduced); names.append(['source',block,held,list(e)])
            all_rows.update(reduced)
        print(json.dumps({'block':block,'held':held,'columns':len(columns),
                         'nonzeros':sum(map(len,columns)),
                         'seconds':round(time.time()-start,2)}),flush=True)
    rhs={(len(support_specs),source_index[encode(e)]):cv(q) for e,q in AQ.items()}
    all_rows.update(rhs)
    rows=sorted(all_rows); row_index={k:i for i,k in enumerate(rows)}
    path=ROOT/f'assembly-{families}-{p}.bin'
    with path.open('wb') as out:
        out.write(struct.pack('<4I',len(rows),len(columns),p,
                              sum(map(len,columns))+len(rhs)))
        for col in columns+[rhs]:
            out.write(struct.pack('<I',len(col)))
            for k,v in col.items(): out.write(struct.pack('<II',row_index[k],v))
    metadata={
        'prime':p,'families':families,'support_specs':support_specs,'rows':len(rows),'columns':len(columns),
        'nonzeros':sum(map(len,columns)), 'seconds':time.time()-start,
        'source_exponents':[list(e) for e in sources],
        'names':names,
        'row_exponents':[[a,list(decode(b)) if a<len(support_specs) else b] for a,b in rows],
        'denominators':denominators,
        'F':[[list(e),str(c)] for e,c in FQ.items()],
        'A':[[list(e),str(c)] for e,c in AQ.items()],
        'identity':'L_Di(Ni)+Ai*Di^2=0 mod F^2; sum Ai=A',
    }
    path.with_suffix('.json').write_text(json.dumps(metadata))
    print(json.dumps({k:v for k,v in metadata.items()
                      if k not in ['names','row_exponents','denominators','F','A','source_exponents']}),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=1000003)
    ap.add_argument('--families',choices=['X','XY'],default='X')
    args=ap.parse_args()
    run(args.prime,args.families)
