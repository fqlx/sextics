#!/usr/bin/env python3
"""Cone-amplitude rank-five current modules in a consistent physical pencil."""
import argparse,json,pickle,random,time,sys
from pathlib import Path
from flint import nmod_mat
HERE=Path(__file__).resolve().parent
sys.path.insert(0,'/workspace/research/round10/horizontal5')
from physical_search import OpenModel,Jet,dot,monomials
from frame import PencilFrame

def labels(args):
    comps=range(5) if args.components=='all' else (range(3,5) if args.components=='boundary' else range(3))
    return [(field,c,e,k,z,r,density) for field in args.fields.split(',') for density in args.densities.split(',') for c in comps for k in range(args.smax+1) for z in range(args.zmax+1) for r in map(int,args.rpowers.split(',')) for e in monomials(args.degree)]

class Model:
    def __init__(self,p,connection):self.p=p;self.base=OpenModel(p,connection);self.pencil=PencilFrame(p)
    def point(self,pt):
        d=self.base.point(pt);q=self.pencil.point(pt);p=self.p;s=q['N1p']/q['N0p']
        assert (s.x,s.d)==(d['s'].x,d['s'].d)
        d['pencil']=q;fields={}
        for name,X in q['fields'].items():
            vals=[t.x for t in X];div=sum(X[i].d[i] for i in range(3))%p
            if name=='radial':
                assert (div+dot(vals,q['Jab'].d,p)*pow(q['Jab'].x,-1,p))%p==0
                assert dot(vals,d['s'].d,p)==0
            if name=='curve_s':assert dot(vals,d['s'].d,p)==1
            if name=='dual_v':assert dot(vals,d['s'].d,p)==0 and vals[2]==1
            N=[[sum(vals[j]*d['openphysical'][j][a][b] for j in range(3))%p for b in range(5)] for a in range(5)]
            fields[name]=(vals,div,N)
        d['radial_fields']=fields;return d

def columns(d,labs,p):
    cache={};rows=[[] for _ in range(5)]
    for name,c,e,k,z,r,density in labs:
        key=(e,k,z,r,density)
        if key not in cache:
            f=Jet(1)
            for i,var in enumerate(('a','b','v')):f*=d['factors'][var]**e[i]
            f*=d['s']**k*d['z']**z*d['pencil']['N0p']**r
            if density in ('rho','cone'):f/=d['fT']
            if density in ('cone','J'):f*=d['pencil']['Jab']
            cache[key]=f
        f=cache[key];X,div,N=d['radial_fields'][name]
        scalar=(dot(X,f.d,p)+(div+dot(X,d['logF'],p))*f.x)%p
        for i in range(5):rows[i].append((f.x*N[c][i]+(scalar if i==c else 0))%p)
    return rows

def run(args):
    start=time.time();p=args.prime;rng=random.Random(args.seed);model=Model(p,args.connection);labs=labels(args);n=len(labs);samples=args.samples or(n//5+35)
    rows=[];rhs=[];pts=[]
    while len(pts)<samples:
        pt=[rng.randrange(1,p) for _ in range(3)]
        try:d=model.point(pt);r=columns(d,labs,p)
        except (ZeroDivisionError,ValueError):continue
        rows.extend(r);rhs.extend(d['correction5'] if args.correction else d['rhs5']);pts.append(pt)
    print(json.dumps({'stage':'matrix','columns':n,'rows':len(rows),'seconds':time.time()-start}),flush=True)
    rank=nmod_mat(rows,p).rank();RR,arank=nmod_mat([row+[y] for row,y in zip(rows,rhs)],p).rref();sol=None;validation=None
    if rank==arank:
        sol=[0]*n
        for i in range(arank):
            pivot=next((j for j in range(n) if RR[i,j]),None)
            if pivot is not None:sol[pivot]=int(RR[i,n])
        validation=True
        for _ in range(20):
            while True:
                pt=[rng.randrange(1,p) for _ in range(3)]
                try:d=model.point(pt);r=columns(d,labs,p);break
                except (ZeroDivisionError,ValueError):pass
            if any(dot(row,sol,p)!=y for row,y in zip(r,d['correction5'] if args.correction else d['rhs5'])):validation=False;break
    result={'args':vars(args),'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'validation20':validation,'seconds':time.time()-start,'scope':'finite-prime cone-amplitude horizontalcurrentmodule only; physicalgraphH20notasserted'}
    out=HERE/args.output;pickle.dump(dict(result=result,labels=labs,points=pts,solution=sol),open(str(out)+'.pickle','wb'));Path(str(out)+'.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--connection',default='/workspace/research/round10/horizontal5/rank5_connection.pickle');ap.add_argument('--fields',default='radial,curve_s,dual_v');ap.add_argument('--components',choices=('all','boundary','proper'),default='all');ap.add_argument('--degree',type=int,default=0);ap.add_argument('--smax',type=int,default=1);ap.add_argument('--zmax',type=int,default=0);ap.add_argument('--rpowers',default='0');ap.add_argument('--densities',default='rho,rhofT,cone');ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--samples',type=int,default=0);ap.add_argument('--seed',type=int,default=1091);ap.add_argument('--output',default='radial_first');ap.add_argument('--correction',action='store_true');run(ap.parse_args())
