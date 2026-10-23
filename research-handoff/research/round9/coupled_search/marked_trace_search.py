#!/usr/bin/env python3
"""Geometric coupled currents from traced marked Prym forms wedge Gamma forms.

All first derivatives of the resulting vector fields are exact finite-field
jets. Second jets of the physical coordinate map are retained when forming
the marked absolute one-forms. No scalar-direction projection is used.
"""
import argparse,json,pickle,random,time
from pathlib import Path
import sympy as sy
from flint import nmod_mat
from search import Model,Jet,Poly,qmod,dot,monomials,HERE

class J2:
    p=1000003
    def __init__(self,x,d=None,h=None):
        self.x=int(x)%self.p;self.d=[int(t)%self.p for t in (d or [0,0])];self.h=[[int(t)%self.p for t in row] for row in (h or [[0,0],[0,0]])]
    def __add__(a,b):
        if not isinstance(b,J2):b=J2(b)
        return J2(a.x+b.x,[a.d[i]+b.d[i] for i in range(2)],[[a.h[i][j]+b.h[i][j] for j in range(2)] for i in range(2)])
    __radd__=__add__
    def __neg__(a):return J2(-a.x,[-t for t in a.d],[[-t for t in row] for row in a.h])
    def __sub__(a,b):return a+-b if isinstance(b,J2) else a+(-b)
    def __rsub__(a,b):return -a+b
    def __mul__(a,b):
        if not isinstance(b,J2):b=J2(b)
        return J2(a.x*b.x,[a.d[i]*b.x+a.x*b.d[i] for i in range(2)],[[a.h[i][j]*b.x+a.d[i]*b.d[j]+a.d[j]*b.d[i]+a.x*b.h[i][j] for j in range(2)] for i in range(2)])
    __rmul__=__mul__
    def __pow__(a,n):
        p=a.p;x=pow(a.x,n,p);c=n*pow(a.x,n-1,p)%p if n else 0;cc=n*(n-1)*pow(a.x,n-2,p)%p if n not in (0,1) else 0
        return J2(x,[c*t for t in a.d],[[c*a.h[i][j]+cc*a.d[i]*a.d[j] for j in range(2)] for i in range(2)])
    def __truediv__(a,b):return a*(b**-1) if isinstance(b,J2) else a*J2(b)**-1
    def __rtruediv__(a,b):return b*a**-1
    def jet(a):return Jet(a.x,a.d+[0])
    def derivative(a,i):return Jet(a.d[i],a.h[i]+[0])

class Quad:
    """a+b*u, u²+c*u+P=0; coefficients are first jets in physical a,b."""
    c=None;P=None
    def __init__(self,a,b=0):self.a=a if isinstance(a,Jet) else Jet(a);self.b=b if isinstance(b,Jet) else Jet(b)
    def __add__(a,b):
        if not isinstance(b,Quad):b=Quad(b)
        return Quad(a.a+b.a,a.b+b.b)
    __radd__=__add__
    def __neg__(a):return Quad(-a.a,-a.b)
    def __sub__(a,b):return a+-b if isinstance(b,Quad) else a+(-b)
    def __rsub__(a,b):return -a+b
    def __mul__(a,b):
        if not isinstance(b,Quad):b=Quad(b)
        return Quad(a.a*b.a-Quad.P*a.b*b.b,a.a*b.b+a.b*b.a-Quad.c*a.b*b.b)
    __rmul__=__mul__
    def inv(a):
        norm=a.a*a.a-Quad.c*a.a*a.b+Quad.P*a.b*a.b
        return Quad((a.a-Quad.c*a.b)/norm,-a.b/norm)
    def __pow__(a,n):
        if n<0:return a.inv()**(-n)
        out=Quad(1)
        while n:
            if n&1:out=out*a
            a=a*a;n//=2
        return out
    def __truediv__(a,b):return a*(b.inv() if isinstance(b,Quad) else Quad(b).inv())
    def __rtruediv__(a,b):return Quad(b)*a.inv()

def compile_primitive(p,primitive_frame='original'):
    out=[]
    for name,indices,char in [('actual',[0,1],1),('conjugate',[0],2)]:
        d=pickle.load(open(HERE.parent/f'cyclic_full/{name}_fast.pickle','rb'));variables=d['symbols'][3:]
        globalframe=pickle.load(open(HERE.parent/'cyclic_full/global_eta_frame.pickle','rb')) if name=='actual' and primitive_frame=='global' else None
        def comp(f):
            n,de=sy.fraction(f);return Poly(sy.Poly(n,*variables).as_dict(),p),Poly(sy.Poly(de,*variables).as_dict(),p)
        for idx in indices:
            directions=[]
            for j in ('L','r','x'):
                pp=d['primitives'][j][idx]
                coeffs=pp['Q8_raw'];denominator=pp['Q8_denominator']
                if globalframe is not None:
                    loc=dict(zip(('L','r','x'),variables))
                    def expr(e):return sy.sympify(e['numerator'].replace('^','**'),locals=loc)/sy.sympify(e['denominator'].replace('^','**'),locals=loc)
                    coeffs=[expr(e) for e in globalframe['hol_primitives'][j][idx]['Jacobian_coefficients']];denominator=sy.Integer(1)
                terms=[]
                for coeff,(component,e) in zip(coeffs,d['lab8']):
                    if component not in (0,1) or coeff==0:continue
                    power=e[0]+int(component==1)
                    assert (power-char)%3==0 and power>=char
                    terms.append((comp(coeff),1 if component==0 else -1,(power-char)//3,e[2]))
                directions.append((terms,comp(denominator)))
            out.append((name,idx,char,directions))
    return out

def ratiojet(pair,pars):
    pt=[x.x for x in pars]
    def evaluate(poly):
        val,grad=poly.eval(pt,True)
        return Jet(val,[sum(grad[j]*pars[j].d[i] for j in range(3)) for i in range(2)]+[0])
    return evaluate(pair[0])/evaluate(pair[1])

def geometric_fields(model,pt,compiled):
    p=model.p;J2.p=p;point=model.point(pt)
    a=J2(pt[0],[1,0]);b=J2(pt[1],[0,1]);v=J2(pt[2]);c=qmod('5/7',p)
    E=1+a*v;B=b*E;P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R;M=A/(3*S)
    L=(27*P*S**2-9*Q*R*S+2*R**3)/(3*A**2);r=(3*S*Q-R**2)/(B*A);x=3*B**3/A;z=B*R/A
    pars=[L,r,x]
    assert [t.x for t in pars]==point['pars']
    for j in range(3):assert pars[j].d==point['J'][j][:2]
    logRho=[(A.derivative(i)/A.jet()-S.derivative(i)/S.jet())/3 for i in range(2)]
    Quad.c=Jet(c);Quad.P=P.jet();u=Quad(0,1);ct=c*u/M.jet()+r.jet()+3*z.jet()**2/x.jet();uM=u/M.jet()
    ct0=c*a.jet()*v.jet()/(M.jet()*E.jet())
    assert (ct.a.x,ct.a.d[:2])==(ct0.x,ct0.d[:2])
    norm=ct.a**2-c*ct.a*ct.b+P.jet()*ct.b**2
    G=P*E**2-c*a*v*E+a*a*v*v
    norm0=c*c*G.jet()/(M.jet()**2*E.jet()**2)
    assert (norm.x,norm.d[:2])==(norm0.x,norm0.d[:2])
    basic=[]
    for name,idx,char,directions in compiled:
        H=[]
        for terms,den in directions:
            value=Quad(0)
            for pair,sign,q,k in terms:value+=sign*Quad(ratiojet(pair,pars))*uM**q*z.jet()**k
            H.append(value/ratiojet(den,pars))
        numerator=[]
        for i in range(2):
            n=-logRho[i]*(z.jet() if name=='actual' and idx==1 else 1)
            numerator.append(Quad(n)+sum((H[j]*pars[j].derivative(i) for j in range(3)),Quad(0)))
        Ri=[n/ct for n in numerator]
        for nn,rr in zip(numerator,Ri):
            closed=(ct.a*nn.b-ct.b*nn.a)/norm
            assert (rr.b.x,rr.b.d[:2])==(closed.x,closed.d[:2])
        # Exact quadratic identity Tr[R/(2u+c)]=coefficient_u(R).
        # Full degree-six trace includes μ3 factor3 and Fw contributes1/3.
        trac=[q.b for q in Ri]
        for j in range(3 if name=='actual' else 4):
            basic.append((f'{name}{idx}_v{j}',[trac[1]*pow(pt[2],j,p),-trac[0]*pow(pt[2],j,p),Jet(0)]))
        if name=='conjugate':basic.append(('conjugate0_u',[Ri[1].a-c*Ri[1].b,-Ri[0].a+c*Ri[0].b,Jet(0)]))
    assert len(basic)==11
    fT=3*a.jet()**3*S.jet()/(2*B.jet()**3*A.jet());point['fT']=fT
    point['markedfields']=basic;point['logRho']=[t.x for t in logRho]+[0]
    return point

def labels(degree,zmax,components,densities):
    out=[];seen=set();groups=[0,0,0,1,1,1,2,2,2,2,3];vpowers=[0,1,2,0,1,2,0,1,2,3,0]
    for density in densities:
        for j in range(11):
            for c in range(components):
                for k in range(zmax+1):
                    for e in monomials(degree):
                        key=(density,groups[j],c,k,e[0],e[1],e[2]+vpowers[j])
                        if key not in seen:seen.add(key);out.append((j,c,e,k,density))
    return out

def columns(point,labs,p):
    rows=[[],[],[]];cache={};pt=point['pt']
    for j,c,e,k,density in labs:
        key=(e,k)
        if key not in cache:
            f=Jet(1)
            for i in range(3):f*=point['factors'][('a','b','v')[i]]**e[i]
            f*=point['z']**k;cache[key]=f
        f=cache[key];_,jets=point['markedfields'][j]
        # Our equations use normalized density rho*fT. Rawrho currents divide
        # the traced vectorfield byfT; this retains all derivative terms.
        if density=='rho':jets=[x/point['fT'] for x in jets]
        X=[x.x for x in jets];div=(jets[0].d[0]+jets[1].d[1])%p
        scalar=(dot(X,f.d,p)+(div+dot(X,point['logF'],p))*f.x)%p
        canon=[sum(point['J'][h][i]*X[i] for i in range(3))%p for h in range(3)]
        conn=[sum(canon[h]*point['N'][h][c][i] for h in range(3))%p for i in range(3)]
        for i in range(3):rows[i].append((f.x*conn[i]+(scalar if i==c else 0))%p)
    return rows

def run(args):
    start=time.time();p=args.prime;rng=random.Random(args.seed);model=Model(p,args.basis);compiled=compile_primitive(p,args.primitive_frame)
    labs=labels(args.degree,args.zmax,args.components,args.densities.split(','));n=len(labs);samples=args.samples or (n//3+35)
    rows=[];rhs=[];pts=[];nonzero=[False]*11
    while len(pts)<samples:
        pt=[rng.randrange(1,p) for _ in range(3)]
        try:d=geometric_fields(model,pt,compiled);r=columns(d,labs,p)
        except (ZeroDivisionError,ValueError):continue
        rows.extend(r);rhs.extend(d['correction'] if args.correction else d['rhs']);pts.append(pt)
        for j,(_,field) in enumerate(d['markedfields']):nonzero[j]|=any(v.x for v in field)
    print(json.dumps({'stage':'matrix','columns':n,'rows':len(rows),'nonzero11':nonzero,'seconds':time.time()-start}),flush=True)
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
                try:d=geometric_fields(model,pt,compiled);r=columns(d,labs,p);break
                except (ZeroDivisionError,ValueError):pass
            if any(dot(row,sol,p)!=y for row,y in zip(r,d['correction'] if args.correction else d['rhs'])):validation=False;break
    result={'args':vars(args),'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'nonzero11':nonzero,'validation20':validation,'seconds':time.time()-start,'scope':'finite-prime full coupled currentmodule tracedfrommarkedpoint; no directmarkeddivisorGysin or source-serving claim'}
    stem=HERE/args.output;pickle.dump(dict(result=result,labels=labs,points=pts,solution=sol),open(str(stem)+'.pickle','wb'));Path(str(stem)+'.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=0);ap.add_argument('--zmax',type=int,default=0);ap.add_argument('--components',type=int,choices=(2,3),default=3);ap.add_argument('--densities',default='rho,rhofT');ap.add_argument('--basis',choices=('eta','theta','global'),default='eta');ap.add_argument('--primitive-frame',choices=('original','global'),default='original');ap.add_argument('--samples',type=int,default=0);ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--seed',type=int,default=975);ap.add_argument('--output',default='marked_first');ap.add_argument('--correction',action='store_true');run(ap.parse_args())
