#!/usr/bin/env python3
"""Complete fixed-D18 system, modulo F^2 and exact gauge reductions.

The quotient and radial gauges are polynomial identities valid in characteristic
zero; only the saved matrix coefficients are reduced modulo the chosen prime.
"""
import argparse, json, struct, sys, time
from pathlib import Path
from collections import defaultdict

sys.path.insert(0, '/workspace/off-paired-research-published')
from ansatz import F as FQ, A as AQ, Q, char, mons

ROOT=Path(__file__).resolve().parent
SHIFT=18
Y=1<<SHIFT
def encode(e): return sum(v<<(6*i) for i,v in enumerate(e))
def decode(k): return tuple((k>>(6*i))&63 for i in range(6))

def run(p):
    started=time.time()
    def cv(q): return q.numerator*pow(q.denominator,-1,p)%p
    F={encode(e):cv(q) for e,q in FQ.items()}
    A={encode(e):cv(q) for e,q in AQ.items()}
    def add(a,b):
        out=dict(a)
        for k,v in b.items():
            v=(out.get(k,0)+v)%p
            if v:out[k]=v
            elif k in out:del out[k]
        return out
    def scale(a,v): return {k:c*v%p for k,c in a.items() if c*v%p}
    def mul(a,b):
        out={}
        for k,c in a.items():
            for l,d in b.items():
                out[k+l]=(out.get(k+l,0)+c*d)%p
        return {k:c for k,c in out.items() if c}
    def der(a,i):
        return {k-(1<<(6*i)):c*((k>>(6*i))&63)%p for k,c in a.items() if ((k>>(6*i))&63)}
    X=[{6<<(6*i):1} for i in range(3)]
    FY={6<<(6*i):1 for i in range(3,6)}
    HX=add(add(X[0],X[1]),X[2])
    T=add(X[1],X[2]);K=mul(X[1],X[2])
    D=add(mul(FY,mul(T,T)),scale(mul(HX,K),16))
    FF=mul(F,F)
    assert FF[12*Y]==1
    FFrest=[(k,c,((k>>SHIFT)&63)) for k,c in FF.items() if k!=12*Y]
    def rem(poly):
        buckets=[{} for _ in range(43)]
        for k,c in poly.items():buckets[(k>>SHIFT)&63][k]=c
        for j in range(42,11,-1):
            for k,c in buckets[j].items():
                base=k-12*Y
                for l,v,l_y in FFrest:
                    kk=base+l; b=buckets[j-12+l_y]
                    b[kk]=(b.get(kk,0)-c*v)%p
            buckets[j].clear()
        return {k:c for bucket in buckets[:12] for k,c in bucket.items() if c}
    FD=mul(F,D)
    Pi=[scale(add(mul(D,der(F,i)),mul(F,der(D,i))),-1) for i in range(6)]
    wA=char(next(iter(AQ)))
    cols=[];names=[];all_rows=set()
    for i in range(6):
        unit=1<<(6*i)
        want=((wA[0]+(0,2,0,1,3,3)[i])%6,(wA[1]+(0,0,1,0,0,5)[i])%6)
        exps=[e for e in mons(19) if e[3]<6 and (i!=3 or e[3]==0) and char(e)==want]
        for e in exps:
            k=encode(e)
            col={k+l:v for l,v in Pi[i].items()}
            if e[i]:
                for l,v in FD.items():
                    kk=k-unit+l
                    col[kk]=(col.get(kk,0)+e[i]*v)%p
            col=rem(col)
            if col:
                cols.append(col);names.append([i,list(e)]);all_rows.update(col)
        print(json.dumps({'stage':'columns','component':i,'columns':len(cols),'nonzeros':sum(map(len,cols)),'seconds':round(time.time()-started,2)}),flush=True)
    rhs=rem(scale(mul(A,mul(D,D)),-1))
    all_rows.update(rhs)
    rows=sorted(all_rows);idx={k:i for i,k in enumerate(rows)}
    path=ROOT/f'system-{p}.bin'
    with path.open('wb') as out:
        out.write(struct.pack('<4I',len(rows),len(cols),p,sum(map(len,cols))+len(rhs)))
        for col in cols+[rhs]:
            out.write(struct.pack('<I',len(col)))
            for k,v in col.items():out.write(struct.pack('<II',idx[k],v))
    metadata={'prime':p,'rows':len(rows),'columns':len(cols),'nonzeros':sum(map(len,cols)),
              'rhs_nonzeros':len(rhs),'seconds':time.time()-started,
              'gauge':'Ni modulo F using Y0^6; radial gauge removes NY0 monomials divisible by Y0',
              'D':[[list(decode(k)),v] for k,v in D.items()],
              'F':[[list(e),str(c)] for e,c in FQ.items()],
              'A':[[list(e),str(c)] for e,c in AQ.items()],
              'names':names,'row_exponents':[list(decode(k)) for k in rows]}
    (ROOT/f'system-{p}.json').write_text(json.dumps(metadata))
    print(json.dumps({k:v for k,v in metadata.items() if k not in ['names','row_exponents','F','A','D']}),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--prime',type=int,default=1000003)
    run(ap.parse_args().prime)
