#!/usr/bin/env python3
"""Exact closed-residue preconditioners plus proper marked-log currents.

The twelve boundary currents are identically residue-closed with the full
rho*fT twist. Their proper extension images are tested with a finite proper
current module. They are exact residue classes, not new Gysin evidence.
"""
import argparse,json,pickle,random,time
from pathlib import Path
from flint import nmod_mat
from log_search import LogModel,columns as log_columns,HERE,dot,monomials
from fresh.physical_candidates import physical as fresh_physical,d,add,scale,wedge,vector,Jet as FJet

OPTIONS=[('1','a'),('1','b'),('1','v'),('a','b'),('a','v'),('b','v')]

def candidates(point,p):
    q=fresh_physical(point,p);A,B,F=q['A'],q['B'],q['F'];kap=q['kappa'];out=[]
    for family in ('w','w4'):
        if family=='w':H=[add(d(B),scale(6*B,kap)),add(d(A),scale(3*A,kap))];T=[6*B,3*A]
        else:
            H=[add(scale(-4*B,d(A)),scale(-3*A*B,kap)),add(add(scale(4,d(B)),scale(-4*A,d(A))),scale(3*(2*B-A*A),kap))];T=[-3*A*B,3*(2*B-A*A)]
        for fname,gname in OPTIONS:
            f=FJet(1,p) if fname=='1' else q[fname];g=q[gname]
            forms=[scale(1/F,add(scale(f,wedge(H[i],d(g))),scale(T[i],wedge(d(f),d(g))))) for i in range(2)]
            out.append((family,fname,gname,[vector(form) for form in forms]))
    return out,q

def pointcolumns(model,pt,labs,p):
    q=model.point(pt);seeds,fresh=candidates(pt,p)
    assert fresh['s_eff'].value()==q['s'].x and fresh['s_eff'].first()==list(q['s'].d)
    rows=log_columns(q,labs,p);assert not any(rows[3]) and not any(rows[4]);rows=rows[:3]
    for family,f,g,Z in seeds:
        # Independently check residue closure using the ASSEMBLED rank5 block,
        # not the explicit residue matrix used by the candidate compiler.
        for out in range(2):
            total=0
            for i in range(3):
                total+=Z[out][i].diff(i).value()+q['logF'][i]*Z[out][i].value()
                total+=sum(q['openphysical'][i][j+3][out+3]*Z[j][i].value() for j in range(2))
            assert total%p==0,('boundary seed closure',pt,family,f,g,out)
        image=[sum(q['openphysical'][i][j+3][out]*Z[j][i].value() for j in range(2) for i in range(3))%p for out in range(3)]
        for i in range(3):rows[i].append(image[i])
    return q,rows

def run(args):
    start=time.time();p=args.prime;rng=random.Random(args.seed);model=LogModel(p,args.connection)
    labs=[(j,c,e,0,0,density) for density in ('rho','rhofT') for j in range(6) for c in range(3) for e in monomials(args.degree)]
    n=len(labs)+12;samples=args.samples or (n//3+30);rows=[];rhs=[];pts=[]
    while len(pts)<samples:
        pt=[rng.randrange(1,p) for _ in range(3)]
        try:q,r=pointcolumns(model,pt,labs,p)
        except (ZeroDivisionError,ValueError):continue
        rows.extend(r);rhs.extend(q['correction5'][:3] if args.correction else q['rhs5'][:3]);pts.append(pt)
    print(json.dumps({'stage':'matrix','rows':len(rows),'columns':n,'seconds':time.time()-start}),flush=True)
    rank=nmod_mat(rows,p).rank();RR,arank=nmod_mat([row+[v] for row,v in zip(rows,rhs)],p).rref();sol=None;validation=None
    if rank==arank:
        sol=[0]*n
        for i in range(arank):
            pivot=next((j for j in range(n) if RR[i,j]),None)
            if pivot is not None:sol[pivot]=int(RR[i,n])
        validation=True
        for _ in range(20):
            while True:
                pt=[rng.randrange(1,p) for _ in range(3)]
                try:q,r=pointcolumns(model,pt,labs,p);break
                except (ZeroDivisionError,ValueError):pass
            if any(dot(row,sol,p)!=v for row,v in zip(r,q['correction5'][:3] if args.correction else q['rhs5'][:3])):validation=False;break
    result={'args':vars(args),'proper_columns':len(labs),'closed_seed_columns':12,'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'validation20':validation,'boundary_closure_checked_against_full_rank5':True,'seconds':time.time()-start,'scope':'finite-prime proper-currentpreconditionermodule; seeds are exactresidueclasses, no newGysinclaim'}
    output=HERE/args.output;pickle.dump(dict(result=result,proper_labels=labs,seed_labels=[(fam,f,g) for fam in ('w','w4') for f,g in OPTIONS],points=pts,solution=sol),open(str(output)+'.pickle','wb'));Path(str(output)+'.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--connection',default=str(HERE/'rank5_connection.pickle'));ap.add_argument('--degree',type=int,default=1);ap.add_argument('--samples',type=int,default=0);ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--seed',type=int,default=1063);ap.add_argument('--output',default='closed_seed_first');ap.add_argument('--correction',action='store_true');run(ap.parse_args())
