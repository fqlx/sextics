#!/usr/bin/env python3
"""Structured rank-five currents from the full marked logarithmic module.

Four universal log fields restrict to the physical graph through six pairwise
normal-defect syzygies. Every derivative of the defects and the graph is kept.
"""
import argparse,json,pickle,random,time
from pathlib import Path
from flint import fmpq_mpoly,nmod_mat
from physical_search import OpenModel,PolyND,CTX,HERE,Jet,qmod,dot,monomials
from jet2 import Jet2,evaluate
FRAME=Path('/workspace/research/round9/marked_log_module/verified.pickle')

def physical_second(model,point):
    p=model.p;Jet2.p=p
    a,b,v=[Jet2(point['pt'][i],[int(i==j) for j in range(3)]) for i in range(3)];c=qmod('5/7',p)
    E=1+a*v;B=b*E;P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R
    L=(27*P*S**2-9*Q*R*S+2*R**3)/(3*A**2);r=(3*S*Q-R**2)/(B*A);x=3*B**3/A;z=B*R/A;pars=[L,r,x]
    mark=evaluate(model.N1,pars+[z])/evaluate(model.N0,pars+[z])
    assert (mark.x,tuple(mark.d))==(point['s'].x,point['s'].d)
    for j in range(3):assert (pars[j].x,pars[j].d)==(point['pars'][j],point['J'][j])
    return pars,mark

class LogModel:
    def __init__(self,p,connection):
        self.base=OpenModel(p,connection);self.p=p;data=pickle.load(open(FRAME,'rb'));self.raw=data
        def comp(e):return PolyND(fmpq_mpoly(e['numerator'],CTX).to_dict(),p),PolyND(fmpq_mpoly(e['denominator'],CTX).to_dict(),p)
        self.fields=[[comp(e) for e in row] for row in data['fields']]
        self.contractions=[[[comp(e) for e in row] for row in M] for M in data['connection_contractions']]
    def point(self,pt):
        d=self.base.point(pt);p=self.p;pars,s=physical_second(self.base,d);args=[Jet(v.x,v.d) for v in pars]+[Jet(s.x,s.d)];vals=[v.x for v in args]
        def ev(pair,grad=False):
            def pp(poly):
                if not grad:return poly.eval(vals)
                val,g=poly.eval(vals,True);return Jet(val,[sum(g[j]*args[j].d[i] for j in range(4))%p for i in range(3)])
            return pp(pair[0])/pp(pair[1]) if grad else pp(pair[0])*pow(pp(pair[1]),-1,p)%p
        V=[]
        for j in range(3):
            row=[]
            for a in range(3):
                gradient=[-sum(d['fields'][m][a]*pars[m].h[n][b]*d['fields'][j][n] for m in range(3) for n in range(3))%p for b in range(3)]
                row.append(Jet(d['fields'][j][a],gradient))
            V.append(row)
        # Differentiate the inverse-Jacobian identity as a second independent
        # consistency check on every physical jet.
        for i in range(3):
            for j in range(3):
                product=sum((Jet(pars[i].d[a],pars[i].h[a])*V[j][a] for a in range(3)),Jet(0))
                assert product.x==int(i==j) and not any(product.d)
        W=[[ev(e,True) for e in row] for row in self.fields]
        X=[[sum((W[i][j]*V[j][a] for j in range(3)),Jet(0)) for a in range(3)] for i in range(4)]
        sd=[Jet(s.d[a],s.h[a]) for a in range(3)]
        psi=[W[i][3]-sum((X[i][a]*sd[a] for a in range(3)),Jet(0)) for i in range(4)]
        C=[[[ev(e) for e in row] for row in M] for M in self.contractions]
        pairs=[]
        for i in range(4):
            for j in range(i+1,4):
                field=[psi[j]*X[i][a]-psi[i]*X[j][a] for a in range(3)]
                matrix=[[(psi[j].x*C[i][a][b]-psi[i].x*C[j][a][b])%p for b in range(5)] for a in range(5)]
                # Both the normal component and allN_s terms cancel exactly.
                assert dot([z.x for z in field],s.d,p)==(psi[j].x*W[i][3].x-psi[i].x*W[j][3].x)%p
                for a in range(5):
                    for b in range(5):assert sum(field[k].x*d['openphysical'][k][a][b] for k in range(3))%p==matrix[a][b]
                pairs.append((field,matrix))
        d['logpairs']=pairs;d['psi']=psi
        return d

def labels(args):
    comps=range(5) if args.components=='all' else (range(3,5) if args.components=='boundary' else range(3))
    return [(j,c,e,k,l,density) for density in args.densities.split(',') for j in range(6) for c in comps for k in range(args.zmax+1) for l in range(args.smax+1) for e in monomials(args.degree)]

def columns(d,labs,p):
    rows=[[] for _ in range(5)];cache={}
    for j,c,e,k,l,density in labs:
        key=(e,k,l,density)
        if key not in cache:
            f=Jet(1)
            for i,name in enumerate(('a','b','v')):f*=d['factors'][name]**e[i]
            f*=d['z']**k*d['s']**l
            if density=='rho':f/=d['fT']
            cache[key]=f
        f=cache[key];field,N=d['logpairs'][j];X=[v.x for v in field]
        div=sum(field[i].d[i] for i in range(3))%p
        scalar=(dot(X,f.d,p)+(div+dot(X,d['logF'],p))*f.x)%p
        for i in range(5):rows[i].append((f.x*N[c][i]+(scalar if i==c else 0))%p)
    return rows

def run(args):
    start=time.time();p=args.prime;rng=random.Random(args.seed);model=LogModel(p,args.connection);labs=labels(args);n=len(labs);samples=args.samples or (n//5+30)
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
    result={'args':vars(args),'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'validation20':validation,'seconds':time.time()-start,'scope':'finite-prime markedlogtangent currentmodule withallnormaldefectderivatives; no unrestrictedclaim'}
    output=HERE/args.output;pickle.dump(dict(result=result,labels=labs,points=pts,solution=sol),open(str(output)+'.pickle','wb'));Path(str(output)+'.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--connection',default=str(HERE/'rank5_connection.pickle'));ap.add_argument('--degree',type=int,default=0);ap.add_argument('--zmax',type=int,default=0);ap.add_argument('--smax',type=int,default=0);ap.add_argument('--components',choices=('all','boundary','proper'),default='all');ap.add_argument('--densities',default='rho,rhofT');ap.add_argument('--samples',type=int,default=0);ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--seed',type=int,default=1049);ap.add_argument('--output',default='log_first');ap.add_argument('--correction',action='store_true');run(ap.parse_args())
