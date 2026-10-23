"""Fast physical first-jet evaluator for exact horizontal 2-form candidates.

All rational circuits are Taylor-evaluated to order two.  This includes the
full s_eff chain rule through physical z=BR/A.  Import candidate() to obtain
the two normalized current vectors and their first jets.
"""
from pathlib import Path
from itertools import product
import pickle,json
import sympy as sp

HERE=Path(__file__).parent
EFF=pickle.load(open('/workspace/research/round9/abel_prym/effective_schiffer.pickle','rb'))
_,_,_,Lsym,rsym,xsym,zsym=EFF['symbols']
eff={key:sp.Poly(EFF[key],Lsym,rsym,xsym,zsym).as_dict() for key in ('N0','N1')}
ZERO=(0,0,0)
class Jet:
    def __init__(self,x=0,p=1000003):
        self.p=p
        self.c=({e:int(v)%p for e,v in x.items() if int(v)%p}
                if isinstance(x,dict) else ({ZERO:int(x)%p} if int(x)%p else {}))
    @classmethod
    def variable(cls,x,i,p):
        e=[0]*3;e[i]=1
        return cls({ZERO:x,tuple(e):1},p)
    def cast(self,x):return x if isinstance(x,Jet) else Jet(x,self.p)
    def __add__(self,x):
        x=self.cast(x);c=dict(self.c)
        for e,v in x.c.items():c[e]=c.get(e,0)+v
        return Jet(c,self.p)
    __radd__=__add__
    def __neg__(self):return Jet({e:-v for e,v in self.c.items()},self.p)
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        x=self.cast(x);c={}
        for e,a in self.c.items():
            for f,b in x.c.items():
                g=tuple(u+v for u,v in zip(e,f))
                if sum(g)<=2:c[g]=c.get(g,0)+a*b
        return Jet(c,self.p)
    __rmul__=__mul__
    def inverse(self):
        c=self.c.get(ZERO,0)
        if not c:raise ZeroDivisionError('jet denominator vanishes')
        iv=pow(c,-1,self.p);h=(self-c)*iv
        return iv*(1-h+h*h)
    def __truediv__(self,x):return self*self.cast(x).inverse()
    def __rtruediv__(self,x):return self.cast(x)*self.inverse()
    def __pow__(self,n):
        if n<0:return self.inverse()**(-n)
        a=self.cast(1);b=self
        while n:
            if n&1:a=a*b
            b=b*b;n>>=1
        return a
    def diff(self,i):
        c={}
        for e,v in self.c.items():
            if e[i]:
                f=list(e);f[i]-=1;c[tuple(f)]=v*e[i]
        return Jet(c,self.p)
    def value(self):return self.c.get(ZERO,0)
    def first(self):return [self.diff(i).value() for i in range(3)]

def d(f):return [f.diff(i) for i in range(3)]
def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(c,a):return [c*x for x in a]
def wedge(a,b):return [a[0]*b[1]-a[1]*b[0],a[0]*b[2]-a[2]*b[0],a[1]*b[2]-a[2]*b[1]]
def vector(form):return [form[2],-form[1],form[0]]

def physical(point,p=1000003):
    a,b,v=[Jet.variable(x,i,p) for i,x in enumerate(point)]
    c=Jet(5,p)/7
    BP=b*(1+a*v);S=1+a**6+b**6
    R=c*(a*b+v*b**3);Q=c*a*b*v
    AP=3*S-BP*R
    H=27*(1+v**6)*S*S-9*Q*R*S+2*R**3
    J=3*S*Q-R*R
    L=H/(3*AP*AP);r=J/(BP*AP);x=3*BP**3/AP;z=BP*R/AP
    vv=(L,r,x,z)
    nums={}
    for key,poly in eff.items():
        value=Jet(0,p)
        for e,coef in poly.items():
            n,den=map(int,sp.fraction(coef));term=Jet(n,p)/den
            for t,k in zip(vv,e):term=term*t**k
            value+=term
        nums[key]=value
    seff=nums['N1']/nums['N0']
    Aq=c*(1+seff);Bq=L+r*seff+seff**3/x
    m=AP/(3*S);F=3*a**3*S/(2*BP**3*AP)
    kappa=scale(1/(3*m),d(m));twist=add(kappa,scale(1/F,d(F)))
    Delta=Aq*Aq-4*Bq
    RA=[[-Aq/(3*Delta),4/(3*Delta)],[2*Bq/(3*Delta),-2*Aq/(3*Delta)]]
    RB=[[(10*Bq-2*Aq*Aq)/(3*Bq*Delta),-2*Aq/(3*Bq*Delta)],[-Aq/(3*Delta),4/(3*Delta)]]
    Rp=[[[RA[j][k]*Aq.diff(i)+RB[j][k]*Bq.diff(i) for k in range(2)]
         for j in range(2)] for i in range(3)]
    return dict(a=a,b=b,v=v,A=Aq,B=Bq,m=m,F=F,s_eff=seff,
                kappa=kappa,twist=twist,R=Rp,N0=nums['N0'],
                L=L,r=r,x=x,z=z,Delta=Delta)

def candidate(point,family='w',f='1',g='v',p=1000003):
    q=physical(point,p);A,B,F=q['A'],q['B'],q['F'];kap=q['kappa']
    f=Jet(1,p) if f=='1' else q[f]
    g=q[g]
    if family=='w':
        H=[add(d(B),scale(6*B,kap)),add(d(A),scale(3*A,kap))]
        T=[6*B,3*A]
    elif family=='w4':
        H=[add(scale(-4*B,d(A)),scale(-3*A*B,kap)),
           add(add(scale(4,d(B)),scale(-4*A,d(A))),scale(3*(2*B-A*A),kap))]
        T=[-3*A*B,3*(2*B-A*A)]
    else:raise ValueError(family)
    forms=[scale(1/F,add(scale(f,wedge(H[i],d(g))),scale(T[i],wedge(d(f),d(g))))) for i in range(2)]
    Z=[vector(form) for form in forms]
    # Every output is a Jet; only its value/first jets are promised because
    # differentiating input second jets has truncated the higher orders.
    return Z,q

def closedness(Z,q):
    out=[]
    for k in range(2):
        value=Jet(0,Z[0][0].p)
        for i in range(3):
            value+=Z[k][i].diff(i)+q['twist'][i]*Z[k][i]
            for j in range(2):value+=q['R'][i][j][k]*Z[j][i]
        out.append(value.value())
    return out

if __name__=='__main__':
    results=[]
    for point in [(1,2,3),(2,3,5),(3,5,7),(5,7,11),(7,11,13)]:
        for fam in ('w','w4'):
            for f,g in [('1','a'),('1','b'),('1','v'),('a','b'),('a','v'),('b','v')]:
                Z,q=candidate(point,fam,f,g)
                val=closedness(Z,q)
                assert val==[0,0],(point,fam,f,g,val)
                results.append(dict(point=point,family=fam,f=f,g=g,closedness=val,
                                    Z=[[x.value() for x in row] for row in Z]))
    report=dict(prime=1000003,tests=len(results),all_pass=True,
                includes_full_s_eff_chain_rule=True,
                includes_rho_and_fT_twist=True,results=results,
                scope='Evaluation audit of exact universal identities pulled to the physical source; proper extension/source matching remains.')
    (HERE/'physical_candidates.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2))
