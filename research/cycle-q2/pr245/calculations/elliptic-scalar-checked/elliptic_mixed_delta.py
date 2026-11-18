"""Three-direction candidate currents with only the true elliptic discriminant denominator.

Candidate Newton support is inferred from the positive target supports. This is a constructive
family only: no denominator/degree restriction on the protected problem follows from it.
"""
import itertools
from math import gcd
from collections import defaultdict
from time import monotonic
P=101; S0=(0,0,0)
def add(a,b):return (a[0]+b[0],a[1]+b[1],a[2]+b[2])
def sub(a,b):return (a[0]-b[0],a[1]-b[1],a[2]-b[2])
def dot(a,b):return a[0]*b[0]+a[1]*b[1]+a[2]*b[2]
class L(dict):
    def __init__(self,d=0):
        if isinstance(d,int): d={S0:d}
        super().__init__({k:v%P for k,v in d.items() if v%P})
    def __add__(self,q):
        d=self.copy()
        for k,v in L(q).items():d[k]=d.get(k,0)+v
        return L(d)
    __radd__=__add__
    def __neg__(self):return L({k:-v for k,v in self.items()})
    def __sub__(self,q):return self+(-L(q))
    def __rsub__(self,q):return L(q)-self
    def __mul__(self,q):
        if isinstance(q,int):return L({k:v*q for k,v in self.items()})
        h=defaultdict(int)
        for i,c in self.items():
            for j,d in q.items():h[add(i,j)]+=c*d
        return L(h)
    __rmul__=__mul__
    def __pow__(self,n):
        if n<0:
            assert len(self)==1
            (k,v),=self.items()
            return L({tuple(i*n for i in k):pow(v,n,P)})
        if n==0:return L(1)
        h=self**(n//2)
        return h*h*(self if n%2 else 1)
    def __truediv__(self,j):return self*pow(j,-1,P)
    def th(self,i):return L({k:v*k[i] for k,v in self.items()})
u,y,t=(L({tuple(int(l==k) for l in range(3)):1}) for k in range(3))
a,b,c,d,e,f=t**-1+u**6*t**3,1+y**6,t+t**-1,u*y/2,y/2,u/2
A=a*e**2*f+b*d*f**2+c*d**2*e
B=-(27*a*a*b*b*c*c+4*a*a*c*e**3+4*a*b*b*f**3+6*a*b*c*d*e*f+4*b*c*c*d**3-d*d*e*e*f*f)/4
D=4*A**3+27*B**2
Ae=(9*a*b*c-d*e*f)/2;Be=a*b*e*f**2+a*c*d*e**2+b*c*d**2*f;Bee=-A/6
De=12*A*A*Ae+54*B*Be
la=lambda w,v: -A*A*w-9*B*v/2
mu=lambda w,v:9*B*w/2-3*A*v
Le,Me=la(Ae,Be),mu(Ae,Be)
dLe=-2*A*Ae**2-9*(Be**2+B*Bee)/2
dMe=3*Ae*Be/2-3*A*Bee
factor= -u**3*y**2*t/24
target=(factor*(dLe*D-Le*De+Le**2+A*Me**2/3),factor*(dMe*D-Me*De))
Dth=[D.th(i) for i in range(3)]
La=[la(A.th(i),B.th(i)) for i in range(3)]
Mu=[mu(A.th(i),B.th(i)) for i in range(3)]
directions=[s for s in itertools.product(range(-2,3),repeat=3) if gcd(*s)==1]
norm=lambda t,s:max(dot(k,s) for k in t)
def bounds(polys, forced, jit=0):
    limits={}
    src=[set(k) for k in forced]
    for s in directions:
        limits[s]=min(norm(set(U),s)-norm(G,s) for U,G in zip(src,polys) if G)+jit*max(abs(c) for c in s)
    unit=[(1,0,0),(0,1,0),(0,0,1)]
    ranges=[range(-limits[tuple(-q for q in s)], limits[s]+1) for s in unit]
    residues=[{tuple(q%6 for q in k) for k in item} for item in src]
    distinct=[{tuple(q%6 for q in z) for z in g} for g in polys]
    possible=[]
    for m in itertools.product(*ranges):
        if any(dot(m,s)>c for s,c in limits.items()):continue
        if any(not all(tuple((q+r)%6 for q,r in zip(v,m)) in R for v in V) for V,R in zip(distinct,residues)):continue
        possible.append(m)
    return possible
def construction(jit=0,limit=900):
    S=monotonic();cols=[]
    for i in range(3):
        p0=La[i]-Dth[i];q1=-La[i]-Dth[i];q0=A*Mu[i]/3
        ps=bounds([set(D)|set(p0),Mu[i]],target,jit)
        qs=bounds([q0,set(D)|set(q1)],target,jit)
        cols.extend((0,i,m,p0,Mu[i]) for m in ps)
        cols.extend((1,i,m,q0,q1) for m in qs)
    print('support sizes Delta/F0/F1; six current columns; time',len(D),len(target[0]),len(target[1]),
          [sum(col[0]==j and col[1]==i for col in cols) for i in range(3) for j in range(2)],round(monotonic()-S,3),flush=True)
    if not cols or len(cols)>limit:return
    from random import Random
    from flint import nmod_mat
    rnd=Random(245)
    sketch_size=len(cols)+48
    rowdata={}
    def projection(key):
        value=rowdata.get(key)
        if value is None:
            value=(rnd.randrange(sketch_size),rnd.randrange(1,P),
                   rnd.randrange(sketch_size),rnd.randrange(1,P))
            rowdata[key]=value
        return value
    M=nmod_mat(sketch_size,len(cols)+1,P)
    def emit(col):
        channel,i,m,a,b=col
        for h,g in enumerate([a+m[i]*D if channel==0 else a,b+m[i]*D if channel==1 else b]):
            for ex,co in g.items():yield (h,add(ex,m)),co
    sources=[[key,co] for h,f in enumerate(target) for ex,co in f.items() for key in [(h,ex)]]
    for colnum in range(len(cols)+1):
        sk=[0]*sketch_size
        for key,co in (sources if colnum==len(cols) else emit(cols[colnum])):
            i,w,j,v=projection(key);sk[i]+=w*co;sk[j]+=v*co
        for i,v in enumerate(sk):
            if v%P:M[i,colnum]=v%P
    print('original rows, sketch matrix shape, assembly seconds',len(rowdata),sketch_size,len(cols),round(monotonic()-S,3),flush=True)
    red,rr=M.rref()
    possible=not (red[rr-1,len(cols)] and all(not red[rr-1,j] for j in range(len(cols))))
    print('sketch augmented rank, consistent, seconds',rr,possible,round(monotonic()-S,3),flush=True)
    if possible:
        h={}
        j=0
        for i in range(rr):
            while j<len(cols) and not red[i,j]:j+=1
            if j==len(cols):break
            if red[i,len(cols)]:h[j]=int(red[i,len(cols)])
            j+=1
        error=defaultdict(int)
        for i,k in h.items():
            for key,v in emit(cols[i]):error[key]+=k*v
        for key,v in sources:error[key]-=v
        bad=sum(1 for v in error.values() if v%P)
        print('current nonzeros, unsketched errors',len(h),bad,flush=True)
        if not bad:print('modular solution:',[(cols[i][:3],v) for i,v in h.items()],flush=True)
if __name__=='__main__':construction(limit=1800)
