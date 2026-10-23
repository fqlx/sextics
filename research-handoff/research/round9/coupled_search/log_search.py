#!/usr/bin/env python3
"""Complete rank-three coupled operator in a structured logarithmic field module."""
import argparse,json,pickle,random,time
from pathlib import Path
import sympy as s
from flint import nmod_mat
from search import Model,Poly,Jet,dot,monomials,HERE
from higgs_search import gauge

FRAME=HERE.parent/'cyclic_full/elliptic_log_fields.pickle'

def frame(model,intersection=True):
    p=pickle.load(open(FRAME,'rb'));variables=p['variables'];L,r,x=variables;D1=27*L**2+4*r**3*x;D2=p['D'];Xs=p['fields']
    gs=[sum(X[i]*s.diff(D1,variables[i]) for i in range(3)) for X in Xs]
    if intersection:
        fields=[D1*X for X in Xs]+[gs[j]*Xs[i]-gs[i]*Xs[j] for i in range(3) for j in range(i+1,3)]
    else:fields=Xs
    exact=[];compiled=[]
    for X in fields:
        X=[s.expand(t) for t in X];div=s.expand(sum(s.diff(X[i],variables[i]) for i in range(3)))
        assert not s.rem(sum(X[i]*s.diff(D2,variables[i]) for i in range(3)),D2,*variables)
        if intersection:assert not s.rem(sum(X[i]*s.diff(D1,variables[i]) for i in range(3)),D1,*variables)
        exact.append({'field':X,'divergence':div})
        compiled.append(([Poly(s.Poly(t,*variables).as_dict(),model.p) for t in X],Poly(s.Poly(div,*variables).as_dict(),model.p)))
    pickle.dump({'variables':variables,'intersectionD1':intersection,'D1':D1,'D2':D2,'fields':exact,'exact_log_remainders_zero':True},open(HERE/('log_intersection_frame.pickle' if intersection else 'log_D2_frame.pickle'),'wb'))
    return compiled

def point(model,pt,compiled):
    d=model.point(pt);p=model.p;phi=[dot(f,d['logH'],p) for f in d['fields']];Xds=[]
    for X,div in compiled:
        v=[z.eval(d['pars']) for z in X];dr=div.eval(d['pars']);weight=(dr+dot(v,phi,p))%p
        physical=[sum(v[j]*d['fields'][j][i] for j in range(3))%p for i in range(3)]
        conn=[[sum(v[j]*d['N'][j][c][i] for j in range(3))%p for i in range(3)] for c in range(3)]
        Xds.append((physical,weight,conn))
    d['logfields']=Xds;return d

def labels(d,eta,zmax,gauges,nfields):return [(j,c,k,e,g) for j in range(nfields) for c in range(3) for g in gauges for k in range(zmax+1) for e in monomials(d if c<2 else eta)]

def columns(d,labs,p):
    cache={};rows=[[],[],[]]
    for j,c,k,e,g in labs:
        key=(k,e,g)
        if key not in cache:
            f=Jet(1)
            for t in range(3):f*=d['factors'][('a','b','v')[t]]**e[t]
            f*=d['z']**k*gauge(g,d);cache[key]=f
        f=cache[key];field,weight,conn=d['logfields'][j]
        scalar=(dot(field,f.d,p)+weight*f.x)%p
        for i in range(3):rows[i].append((f.x*conn[c][i]+(scalar if i==c else 0))%p)
    return rows

def run(args):
    start=time.time();p=args.prime;rng=random.Random(args.seed);model=Model(p,args.basis);compiled=frame(model,not args.onlyD2)
    labs=labels(args.degree,args.eta,args.zmax,args.gauges.split(';'),len(compiled));n=len(labs);samples=args.samples or (n//3+35)
    rows=[];rhs=[];pts=[]
    while len(pts)<samples:
        pt=[rng.randrange(1,p) for _ in range(3)]
        try:d=point(model,pt,compiled);r=columns(d,labs,p)
        except (ZeroDivisionError,ValueError):continue
        rows.extend(r);rhs.extend(d['correction']);pts.append(pt)
    print(json.dumps({'stage':'matrix','columns':n,'rows':len(rows),'seconds':time.time()-start}),flush=True)
    rank=nmod_mat(rows,p).rank();RR,arank=nmod_mat([row+[y] for row,y in zip(rows,rhs)],p).rref();sol=None;validation=None
    if arank==rank:
        sol=[0]*n
        for i in range(arank):
            pivot=next((j for j in range(n) if RR[i,j]),None)
            if pivot is not None:sol[pivot]=int(RR[i,n])
        validation=True
        for _ in range(20):
            while True:
                pt=[rng.randrange(1,p) for _ in range(3)]
                try:d=point(model,pt,compiled);r=columns(d,labs,p);break
                except (ZeroDivisionError,ValueError):pass
            if any(dot(row,sol,p)!=y for row,y in zip(r,d['correction'])):validation=False;break
    result={'args':vars(args),'nfields':len(compiled),'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'validation20':validation,'seconds':time.time()-start,'scope':'finite-prime sampled full-rank-three logarithmic current module; all field tangencies verified exactly QQ'}
    stem=HERE/args.output;pickle.dump(dict(result=result,labels=labs,points=pts,solution=sol),open(str(stem)+'.pickle','wb'));Path(str(stem)+'.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=3);ap.add_argument('--eta',type=int,default=1);ap.add_argument('--zmax',type=int,default=2);ap.add_argument('--gauges',default='1');ap.add_argument('--basis',choices=('eta','theta','global'),default='eta');ap.add_argument('--onlyD2',action='store_true');ap.add_argument('--samples',type=int,default=0);ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--seed',type=int,default=963);ap.add_argument('--output',default='log_first');run(ap.parse_args())
