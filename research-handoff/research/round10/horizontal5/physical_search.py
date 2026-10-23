#!/usr/bin/env python3
"""Physical source search in the rank-five horizontal/open-curve extension.

The graph coordinate s is substituted by the source-bound effective point,
with every base derivative retained. Boundary components impose the closed
residue-current equations; proper components retain the source and GM terms.
"""
import argparse,json,pickle,random,time,sys
from pathlib import Path
import sympy as sy
from flint import nmod_mat,fmpq_mpoly_ctx,fmpq_mpoly
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent.parent/'round9/coupled_search'))
from search import Model,Jet,qmod,dot,monomials
CTX=fmpq_mpoly_ctx.get(('L','r','x','s'))

class PolyND:
    def __init__(self,data,p):self.p=p;self.d=[(tuple(e),qmod(c,p)) for e,c in data.items()];self.dim=len(self.d[0][0]) if self.d else 4
    def eval(self,point,gradient=False):
        powers=[]
        for i in range(len(point)):
            pw=[1]
            for _ in range(max((e[i] for e,c in self.d),default=0)):pw.append(pw[-1]*point[i]%self.p)
            powers.append(pw)
        val=0;grad=[0]*len(point)
        for e,c in self.d:
            t=c
            for i in range(len(point)):t=t*powers[i][e[i]]%self.p
            val+=t
            if gradient:
                for i in range(len(point)):
                    if not e[i]:continue
                    u=c*e[i]
                    for j in range(len(point)):u=u*powers[j][e[j]-int(i==j)]%self.p
                    grad[i]+=u
        return (val%self.p,[t%self.p for t in grad]) if gradient else val%self.p

class OpenModel:
    def __init__(self,p,connection):
        self.p=p;self.proper=Model(p,'global');self.raw=pickle.load(open(connection,'rb'))
        assert self.raw['exact_curvature'] is not None and not any(self.raw['exact_curvature'].values())
        self.conn={}
        for name,M in self.raw['connection'].items():
            self.conn[name]=[[(PolyND(fmpq_mpoly(e['numerator'],CTX).to_dict(),p),PolyND(fmpq_mpoly(e['denominator'],CTX).to_dict(),p)) for e in row] for row in M]
        effective=pickle.load(open('/workspace/research/round9/abel_prym/effective_schiffer.pickle','rb'));W,h,t,L,r,x,z=effective['symbols']
        self.N0=PolyND(sy.Poly(effective['N0'],L,r,x,z).as_dict(),p);self.N1=PolyND(sy.Poly(effective['N1'],L,r,x,z).as_dict(),p)
        physical=pickle.load(open('/workspace/research/round9/abel_prym/effective_physical.pickle','rb'))['T_effective_canonical']
        self.physical_mark=(PolyND(physical['num'],p),PolyND(physical['den'],p))
    def point(self,pt):
        d=self.proper.point(pt);p=self.p;pars=[Jet(d['pars'][i],d['J'][i]) for i in range(3)];args=pars+[d['z']];values=[q.x for q in args]
        def jet(poly):
            val,grad=poly.eval(values,True)
            return Jet(val,[sum(grad[j]*args[j].d[i] for j in range(4))%p for i in range(3)])
        n0,n1=jet(self.N0),jet(self.N1);s=n1/n0;openargs=[q.x for q in pars]+[s.x]
        def physicaljet(poly):
            value,gradient=poly.eval(pt,True);return Jet(value,gradient)
        directmark=physicaljet(self.physical_mark[0])/physicaljet(self.physical_mark[1])
        assert (s.x,s.d)==(directmark.x,directmark.d),('effective graph pullback derivative',pt)
        con={}
        for name,M in self.conn.items():con[name]=[[n.eval(openargs)*pow(de.eval(openargs),-1,p)%p for n,de in row] for row in M]
        for name in ('L','r','x'):
            for i in range(3):
                for j in range(3):assert con[name][i][j]==d['N'][('L','r','x').index(name)][i][j]
            for i in range(3):assert not any(con[name][i][3:])
        assert not any(any(row) for row in con['s'][:3])
        physical=[];canonical=[]
        for i in range(3):
            physical.append([[sum(d['J'][k][i]*con[name][a][b] for k,name in enumerate(('L','r','x')))+s.d[i]*con['s'][a][b] for b in range(5)] for a in range(5)])
        for j,name in enumerate(('L','r','x')):
            ds=dot(d['fields'][j],s.d,p)
            canonical.append([[(con[name][a][b]+ds*con['s'][a][b])%p for b in range(5)] for a in range(5)])
        d['openphysical']=physical;d['opencanonical']=canonical;d['s']=s;d['N0']=n0;d['N1']=n1
        a,b,v=[d['factors'][name] for name in ('a','b','v')];d['fT']=3*a**3*d['factors']['S']/(2*d['factors']['B']**3*d['factors']['A'])
        d['rhs5']=d['rhs']+[0,0];d['correction5']=d['correction']+[0,0]
        return d

def labels(args):
    comps=range(5) if args.components=='all' else (range(3,5) if args.components=='boundary' else range(3))
    return [(frame,j,c,e,k,l,density) for frame in args.frames.split(',') for density in args.densities.split(',') for j in range(3) for c in comps for k in range(args.zmax+1) for l in range(args.smax+1) for e in monomials(args.degree)]

def columns(d,labs,p):
    cache={};rows=[[] for _ in range(5)]
    for frame,j,c,e,k,l,density in labs:
        key=(e,k,l,density)
        if key not in cache:
            f=Jet(1)
            for i,name in enumerate(('a','b','v')):f*=d['factors'][name]**e[i]
            f*=d['z']**k*d['s']**l
            if density=='rho':f/=d['fT']
            cache[key]=f
        f=cache[key]
        if frame=='physical':
            scalar=(f.d[j]+d['logF'][j]*f.x)%p;N=d['openphysical'][j]
        else:
            scalar=(dot(d['fields'][j],f.d,p)+dot(d['fields'][j],d['logH'],p)*f.x)%p;N=d['opencanonical'][j]
        for i in range(5):rows[i].append((f.x*N[c][i]+(scalar if i==c else 0))%p)
    return rows

def run(args):
    start=time.time();p=args.prime;rng=random.Random(args.seed);model=OpenModel(p,args.connection);labs=labels(args);n=len(labs);samples=args.samples or (n//5+35)
    rows=[];rhs=[];pts=[]
    while len(pts)<samples:
        pt=[rng.randrange(1,p) for _ in range(3)]
        try:d=model.point(pt);r=columns(d,labs,p)
        except (ZeroDivisionError,ValueError):continue
        rows.extend(r);rhs.extend(d['correction5'] if args.correction else d['rhs5']);pts.append(pt)
    print(json.dumps({'stage':'matrix','rows':len(rows),'columns':n,'seconds':time.time()-start}),flush=True)
    rank=nmod_mat(rows,p).rank();RR,arank=nmod_mat([row+[y] for row,y in zip(rows,rhs)],p).rref();sol=None;validation=None
    if rank==arank:
        sol=[0]*n
        for i in range(arank):
            pivot=next((j for j in range(n) if RR[i,j]),None)
            if pivot is not None:sol[pivot]=int(RR[i,n])
        validation=True
        for _ in range(25):
            while True:
                pt=[rng.randrange(1,p) for _ in range(3)]
                try:d=model.point(pt);r=columns(d,labs,p);break
                except (ZeroDivisionError,ValueError):pass
            if any(dot(row,sol,p)!=y for row,y in zip(r,d['correction5'] if args.correction else d['rhs5'])):validation=False;break
    result={'args':vars(args),'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'validation25':validation,'seconds':time.time()-start,'scope':'finite-prime sampled rank5 horizontalcurrentmodule; positive requires QQreconstruction'}
    output=HERE/args.output;pickle.dump(dict(result=result,labels=labs,points=pts,solution=sol),open(str(output)+'.pickle','wb'));Path(str(output)+'.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--connection',default=str(HERE/'rank5_connection.pickle'));ap.add_argument('--degree',type=int,default=0);ap.add_argument('--zmax',type=int,default=0);ap.add_argument('--smax',type=int,default=0);ap.add_argument('--components',choices=('all','boundary','proper'),default='all');ap.add_argument('--frames',default='physical');ap.add_argument('--densities',default='rho,rhofT');ap.add_argument('--samples',type=int,default=0);ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--seed',type=int,default=1031);ap.add_argument('--output',default='first_physical');ap.add_argument('--correction',action='store_true');run(ap.parse_args())
