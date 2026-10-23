#!/usr/bin/env python3
"""Five rational holomorphic current generators with exactly zero eta output.

For (j,c)!=(x,1), K_jc=(e_c along j) - x^2 N_j[c,2](e_1 along x).
The eta cancellation follows from N_x[1,:]=(0,0,1/x^2). All coefficient
derivatives and the complete twisted divergence weight are retained.
"""
import argparse,json,pickle,random,time,re
from pathlib import Path
from flint import nmod_mat
from search import Model,Jet,dot,monomials,HERE

def gauge(label,point):
    z=Jet(1)
    if label=='1':return z
    for t in label.split('*'):
        m=re.fullmatch(r'([a-zA-Z][a-zA-Z0-9]*)(?:\^(-?\d+))?',t)
        if not m:raise ValueError(label)
        z*=point['factors'][m[1]]**int(m[2] or 1)
    return z

def buildpoint(model,pt):
    p=model.p;point=model.point(pt);par=point['pars'];x=par[2]
    point['phi']=[dot(f,point['logH'],p) for f in point['fields']]
    ker=[]
    for j,c in [(j,c) for j in range(3) for c in range(2) if (j,c)!=(2,1)]:
        num,den=model.conn[j][3*c+2]
        nv,ng=num.eval(par,True);dv,dg=den.eval(par,True);dinv=pow(dv,-1,p)
        h=nv*dinv%p;hx=(ng[2]*dv-nv*dg[2])*dinv*dinv%p
        assert h==point['N'][j][c][2]
        q=-x*x*h%p;qx=(-2*x*h-x*x*hx)%p
        assert (h+q*pow(x,-2,p))%p==0
        ker.append((j,c,q,qx))
    point['kernel']=ker
    return point

def labels(d,zmax,gauges):return [(i,k,e,g) for i in range(5) for g in gauges for k in range(zmax+1) for e in monomials(d)]

def columns(point,labs,p):
    feature={};rows=[[],[]];pt=point['pt'];z=point['z'];fields=point['fields'];N=point['N'];phi=point['phi']
    for i,k,e,g in labs:
        key=(k,e,g)
        if key not in feature:
            f=Jet(1)
            for j in range(3):f*=point['factors'][('a','b','v')[j]]**e[j]
            f*=z**k*gauge(g,point)
            feature[key]=(f.x,[dot(field,f.d,p) for field in fields])
        f,df=feature[key];j,c,q,qx=point['kernel'][i]
        # N_x[1,0:2]=0, so the pivot correction contributes only to omega1.
        y=[f*N[j][c][t]%p for t in range(2)]
        y[c]=(y[c]+df[j]+phi[j]*f)%p
        y[1]=(y[1]+qx*f+q*df[2]+phi[2]*q*f)%p
        for t in range(2):rows[t].append(y[t])
    return rows

def run(args):
    start=time.time();p=args.prime;rng=random.Random(args.seed);model=Model(p)
    gauges=args.gauges.split(';');labs=labels(args.degree,args.zmax,gauges);n=len(labs);samples=args.samples or (n//2+40)
    rows=[];rhs=[];pts=[]
    while len(pts)<samples:
        pt=[rng.randrange(1,p) for _ in range(3)]
        try:point=buildpoint(model,pt);r=columns(point,labs,p)
        except (ZeroDivisionError,ValueError):continue
        rows.extend(r);rhs.extend(point['correction'][:2]);pts.append(pt)
    print(json.dumps({'stage':'matrix','columns':n,'rows':len(rows),'seconds':time.time()-start}),flush=True)
    rank=nmod_mat(rows,p).rank();RR,arank=nmod_mat([row+[v] for row,v in zip(rows,rhs)],p).rref()
    solution=None;validation=None
    if rank==arank:
        solution=[0]*n
        for i in range(arank):
            piv=next((j for j in range(n) if RR[i,j]),None)
            if piv is not None:solution[piv]=int(RR[i,n])
        validation=True
        for _ in range(20):
            while True:
                pt=[rng.randrange(1,p) for _ in range(3)]
                try:point=buildpoint(model,pt);r=columns(point,labs,p);break
                except (ZeroDivisionError,ValueError):pass
            if any(dot(row,solution,p)!=v for row,v in zip(r,point['correction'][:2])):validation=False;break
    result={'args':vars(args),'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'validation20':validation,'seconds':time.time()-start,'scope':'finite-prime sampled five-generator holomorphic Higgs-kernel module only'}
    stem=HERE/args.output;stem.parent.mkdir(parents=True,exist_ok=True)
    pickle.dump(dict(result=result,labels=labs,points=pts,solution=solution),open(str(stem)+'.pickle','wb'));Path(str(stem)+'.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=1);ap.add_argument('--zmax',type=int,default=2);ap.add_argument('--gauges',default='1');ap.add_argument('--samples',type=int,default=0);ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--seed',type=int,default=947);ap.add_argument('--output',default='higgs_first');run(ap.parse_args())
