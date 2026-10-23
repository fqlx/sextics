#!/usr/bin/env python3
"""Exact finite-field samples of the actual full rank-three coupled PDE.

Positive sampled solutions require further point checks and QQ reconstruction.
Negative results describe only the explicitly selected finite current module.
No finite-prime rank difference is promoted to an unrestricted obstruction.
"""
import argparse, json, pickle, random, time
from fractions import Fraction
from pathlib import Path
import sympy as sy
from flint import nmod_mat

HERE=Path(__file__).resolve().parent
GM=HERE.parent/'cyclic_full/actual_fast.pickle'
POLYS=Path('/workspace/research/round8/coupled_source/jacobian_native.pickle')

def qmod(x,p):
    x=Fraction(str(x)); return x.numerator*pow(x.denominator,-1,p)%p

class Jet:
    p=1000003
    def __init__(self,x,d=None): self.x=int(x)%self.p; self.d=tuple(int(t)%self.p for t in (d or (0,0,0)))
    def __add__(a,b):
        if not isinstance(b,Jet):b=Jet(b)
        return Jet(a.x+b.x,[a.d[i]+b.d[i] for i in range(3)])
    __radd__=__add__
    def __neg__(a):return Jet(-a.x,[-t for t in a.d])
    def __sub__(a,b):return a+-b if isinstance(b,Jet) else a+(-b)
    def __rsub__(a,b):return -a+b
    def __mul__(a,b):
        if not isinstance(b,Jet):b=Jet(b)
        return Jet(a.x*b.x,[a.d[i]*b.x+a.x*b.d[i] for i in range(3)])
    __rmul__=__mul__
    def __pow__(a,n):
        x=pow(a.x,n,a.p)
        c=(n*pow(a.x,n-1,a.p))%a.p if n else 0
        return Jet(x,[c*t for t in a.d])
    def __truediv__(a,b):return a*(b**-1) if isinstance(b,Jet) else a*Jet(b)**-1
    def __rtruediv__(a,b):return b*a**-1

class Poly:
    def __init__(self,d,p):self.p=p;self.d=[(tuple(e),qmod(c,p)) for e,c in d.items()]
    def eval(self,pt,gradient=False):
        maxima=[max((e[i] for e,c in self.d),default=0) for i in range(3)]
        pw=[[1] for _ in range(3)]
        for i in range(3):
            for _ in range(maxima[i]):pw[i].append(pw[i][-1]*pt[i]%self.p)
        val=0;g=[0,0,0]
        for e,c in self.d:
            val+=c*pw[0][e[0]]*pw[1][e[1]]*pw[2][e[2]]
            if gradient:
                for i in range(3):
                    if e[i]:g[i]+=c*e[i]*pw[i][e[i]-1]*pw[(i+1)%3][e[(i+1)%3]]*pw[(i+2)%3][e[(i+2)%3]]
        return (val%self.p,[t%self.p for t in g]) if gradient else val%self.p

def dot(a,b,p):return sum(x*y for x,y in zip(a,b))%p
def cross(a,b,p):return [(a[1]*b[2]-a[2]*b[1])%p,(a[2]*b[0]-a[0]*b[2])%p,(a[0]*b[1]-a[1]*b[0])%p]

class Model:
    def __init__(self,p,basis='eta'):
        self.p=p;Jet.p=p
        self.data=pickle.load(open(GM,'rb'));self.symbols=self.data['symbols'][3:]
        if basis in ('theta','global'):
            theta=pickle.load(open(HERE.parent/('cyclic_full/theta_frame.pickle' if basis=='theta' else 'cyclic_full/global_eta_frame.pickle'),'rb'))
            loc=dict(zip(('L','r','x'),self.symbols))
            def expression(e):return sy.sympify(e['numerator'].replace('^','**'),locals=loc)/sy.sympify(e['denominator'].replace('^','**'),locals=loc)
            self.data['connection']={name:sy.Matrix([[expression(e) for e in row] for row in mat]) for name,mat in theta['connection'].items()}
        self.conn=[]
        for j in ('L','r','x'):
            mat=[]
            for t in self.data['connection'][j]:
                n,d=sy.fraction(t)
                mat.append((Poly(sy.Poly(n,*self.symbols).as_dict(),p),Poly(sy.Poly(d,*self.symbols).as_dict(),p)))
            self.conn.append(mat)
        self.polys={k:Poly(d,p) for k,d in pickle.load(open(POLYS,'rb')).items() if k in ('A','B','E','S','R','Delta47')}
        L,r,x=self.symbols
        elliptic=pickle.load(open(HERE.parent/'cyclic_full/elliptic_log_fields.pickle','rb'))
        self.canonical_factors={'D1':Poly(sy.Poly(27*L**2+4*r**3*x,*self.symbols).as_dict(),p),'D2':Poly(sy.Poly(elliptic['D'],*self.symbols).as_dict(),p)}
    def point(self,pt):
        p=self.p
        a,b,v=[Jet(pt[i],[int(i==j) for j in range(3)]) for i in range(3)]
        c=Jet(qmod('5/7',p));E=1+a*v;B=b*E;P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R
        L=(27*P*S**2-9*Q*R*S+2*R**3)/(3*A**2)
        r=(3*S*Q-R**2)/(B*A);x=3*B**3/A;z=B*R/A
        pars=[L,r,x];J=[list(t.d) for t in pars]
        cof=[cross(J[1],J[2],p),cross(J[2],J[0],p),cross(J[0],J[1],p)]
        det=dot(J[0],cof[0],p); inv=pow(det,-1,p)
        fields=[[t*inv%p for t in row] for row in cof]
        # fields[j] is the physical vector field dual to d(pars[j]).
        for i in range(3):
            for j in range(3):assert dot(J[i],fields[j],p)==int(i==j)
        Delta,dDelta=self.polys['Delta47'].eval(pt,True)
        inv3=pow(3,-1,p)
        logH=[(3*a.d[i]*pow(a.x,-1,p)+13*inv3*A.d[i]*pow(A.x,-1,p)-5*b.d[i]*pow(b.x,-1,p)-4*E.d[i]*pow(E.x,-1,p)-4*inv3*S.d[i]*pow(S.x,-1,p)-dDelta[i]*pow(Delta,-1,p))%p for i in range(3)]
        logF=[(3*a.d[i]*pow(a.x,-1,p)+2*inv3*S.d[i]*pow(S.x,-1,p)-3*b.d[i]*pow(b.x,-1,p)-3*E.d[i]*pow(E.x,-1,p)-2*inv3*A.d[i]*pow(A.x,-1,p))%p for i in range(3)]
        # Check native exact Jacobian factorization at every sampled point.
        expect=qmod('1215/343',p)*b.x**2*E.x*S.x**2*Delta*pow(A.x,-5,p)%p
        assert det==expect
        N=[];parpt=[t.x for t in pars]
        for mat in self.conn:
            vals=[n.eval(parpt)*pow(d.eval(parpt),-1,p)%p for n,d in mat]
            N.append([vals[3*i:3*i+3] for i in range(3)])
        # N_j^T e_i is row i of N_j.
        rhs=[(-N[1][1][i]+2*z.x*N[1][0][i]-z.x*z.x*N[0][0][i])%p for i in range(3)]
        phi=[dot(f,logH,p) for f in fields];dz=[dot(f,z.d,p) for f in fields]
        fixed=[[-z.x*z.x,0,0],[2*z.x,-1,0],[0,0,0]]
        fixedgrad=[[-2*z.x*dz[0],0,0],[2*dz[1],0,0],[0,0,0]]
        fixedimage=[sum(fixedgrad[j][i]+phi[j]*fixed[j][i]+sum(N[j][k][i]*fixed[j][k] for k in range(3)) for j in range(3))%p for i in range(3)]
        correction=[(-2*dz[1]-2*z.x*phi[1]+2*z.x*dz[0]+z.x*z.x*phi[0])%p,phi[1],0]
        assert [(rhs[i]-fixedimage[i])%p for i in range(3)]==correction
        factors={'a':a,'b':b,'v':v,'A':A,'B':B,'E':E,'S':S,'R':R,'Delta':Jet(Delta,dDelta)}
        for name,poly in self.canonical_factors.items():
            val,grad=poly.eval(parpt,True)
            factors[name]=Jet(val,[sum(grad[j]*J[j][i] for j in range(3))%p for i in range(3)])
        return dict(pt=pt,z=z,fields=fields,J=J,N=N,logH=logH,logF=logF,rhs=rhs,correction=correction,pars=parpt,factors=factors)

def monomials(d):return [(i,j,k) for i in range(d+1) for j in range(d+1-i) for k in range(d+1-i-j)] if d>=0 else []

def labels(d,eta,zmax=2,frames=('canonical',)):
    return [(frame,j,comp,k,e) for frame in frames for j in range(3) for comp in range(3) for k in range(zmax+1) for e in monomials(d if comp<2 else eta)]

def sample_columns(point,labs,p):
    pt=point['pt'];z=point['z'];N=point['N'];rows=[[],[],[]]
    feature={}
    for frame,j,comp,k,e in labs:
        key=(k,e)
        if key not in feature:
            val=1; grad=[0,0,0]
            for i in range(3):val=val*pow(pt[i],e[i],p)%p
            for i in range(3):
                if e[i]:grad[i]=val*e[i]*pow(pt[i],-1,p)%p
            zpow=pow(z.x,k,p);derk=(k*pow(z.x,k-1,p))%p if k else 0
            feature[key]=(val*zpow%p,[(grad[i]*zpow+val*derk*z.d[i])%p for i in range(3)])
        val,grad=feature[key]
        if frame=='canonical':
            deriv=dot(point['fields'][j],grad,p);log=dot(point['fields'][j],point['logH'],p);conn=N[j][comp]
        else:
            deriv=grad[j];log=point['logF'][j];conn=[sum(point['J'][h][j]*N[h][comp][i] for h in range(3))%p for i in range(3)]
        for i in range(3):rows[i].append((val*conn[i]+(deriv+log*val if i==comp else 0))%p)
    return rows

def run(args):
    start=time.time();p=args.prime;rng=random.Random(args.seed);model=Model(p,args.basis)
    frames=tuple(args.frames.split(','));labs=labels(args.degree,args.eta,args.zmax,frames);n=len(labs)
    samples=args.samples or (n//3+30)
    rows=[];points=[];rhs=[]
    while len(points)<samples:
        pt=[rng.randrange(1,p) for _ in range(3)]
        try:point=model.point(pt)
        except (ZeroDivisionError,ValueError):continue
        r=sample_columns(point,labs,p);y=point['rhs'] if not args.correction else point['correction']
        rows.extend(r);rhs.extend(y);points.append(pt)
    print(json.dumps({'stage':'matrix','columns':n,'rows':len(rows),'samples':samples,'seconds':time.time()-start}),flush=True)
    A=nmod_mat(rows,p);rank=A.rank();aug=nmod_mat([row+[y] for row,y in zip(rows,rhs)],p)
    RR,arank=aug.rref();solution=None;validation=None
    if arank==rank:
        solution=[0]*n
        for i in range(arank):
            piv=next((j for j in range(n) if RR[i,j]),None)
            if piv is not None:solution[piv]=int(RR[i,n])
        validation=True
        for _ in range(20):
            while True:
                pt=[rng.randrange(1,p) for _ in range(3)]
                try:point=model.point(pt);break
                except (ZeroDivisionError,ValueError):pass
            r=sample_columns(point,labs,p);y=point['rhs'] if not args.correction else point['correction']
            if any(dot(row,solution,p)!=want for row,want in zip(r,y)):validation=False;break
    result={'args':vars(args),'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'validation20':validation,'seconds':time.time()-start,'scope':'finite-prime sampled current module only; positive requires exact reconstruction'}
    stem=HERE/args.output;stem.parent.mkdir(parents=True,exist_ok=True)
    pickle.dump(dict(result=result,labels=labs,points=points,solution=solution),open(str(stem)+'.pickle','wb'))
    Path(str(stem)+'.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=1);ap.add_argument('--eta',type=int,default=0);ap.add_argument('--zmax',type=int,default=2);ap.add_argument('--frames',default='canonical');ap.add_argument('--basis',choices=('eta','theta','global'),default='eta');ap.add_argument('--samples',type=int,default=0);ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--seed',type=int,default=921);ap.add_argument('--output',default='first');ap.add_argument('--correction',action='store_true');run(ap.parse_args())
