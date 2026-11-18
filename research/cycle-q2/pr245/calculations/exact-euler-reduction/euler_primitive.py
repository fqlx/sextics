"""Derive the exact physical relative primitive for the genus-ten source Euler identity."""
from fractions import Fraction as Q
class L(dict):
    def __init__(self,x=0):
        super().__init__(x if isinstance(x,dict) else ({(0,0):Q(x)} if x else {}))
    def __add__(self,v):
        w=L(self)
        for e,a in L(v).items():
            w[e]=w.get(e,0)+a
            if not w[e]:del w[e]
        return w
    __radd__=__add__
    def __neg__(self):return L({e:-c for e,c in self.items()})
    def __sub__(self,v):return self+-L(v)
    def __rsub__(self,v):return L(v)+-self
    def __mul__(self,v):
        r={}
        for e,a in self.items():
            for f,c in L(v).items():
                q=(e[0]+f[0],e[1]+f[1]);r[q]=r.get(q,0)+a*c
        return L({e:a for e,a in r.items() if a})
    __rmul__=__mul__
    def __pow__(self,k):
        if k<0:
            assert len(self)==1
            e,v=next(iter(self.items()))
            return L({(k*e[0],k*e[1]):Q(v)**k})
        a=L(1)
        for _ in range(k):a=a*self
        return a
    def d(self,j):
        r={}
        for e,a in self.items():
            if e[j]:
                f=list(e);f[j]-=1;r[tuple(f)]=e[j]*a
        return L(r)
    def integral(self,j):
        r={}
        for e,a in self.items():
            assert e[j]!=-1,(e,a)
            f=list(e);f[j]+=1;r[tuple(f)]=Q(a,f[j])
        return L(r)
T=L({(1,0):1});H=L({(0,1):1})
v=(H-6+6*T**2)*T**-1
U=T*v**3
hT=-12*T+Q(2,3)*v
def T_at_U(g):return g.d(0)+hT*g.d(1)
def B(g):return -6*T**2*H**-1*T_at_U(g)
P=2*B(T*H**-1)
g=P*Q(1,3)+(T+T**-1+Q(1,3)*v)*B(P)
Wx=g*U.d(0)-U*T_at_U(P)
Wh=g*U.d(1)
t=T**2
a={5:22394880*(t-1)**2*(2*t+1)**3*(3*t-1),
   4:1244160*(t-1)*(2*t+1)*(138*t**3-7*t**2-13*t-10),
   3:124416*(679*t**4-215*t**3-141*t**2-34*t-19),
   2:6912*(1427*t**3-201*t**2-36*t+25),
   1:576*(927*t**2-32*t-7)}
C=sum(Q(1,3*k)*a[k]*H**-k for k in a)-Q(16,3)*H
etax=(C+64)*T**-1+9952*T
etah=(1728*t-48)*H**-1+288
alpha,beta=etax-Wx,etah-Wh
curv=beta.d(0)-alpha.d(1)
print('curvature coefficients',len(curv), sorted(curv.items())[:8])
assert not curv
R=alpha.integral(0)
rest=beta-R.d(1)
assert all(e[0]==0 for e in rest)
R+=rest.integral(1)
assert R.d(0)==alpha and R.d(1)==beta
print('Exact Laurent primitive size:',len(R))
print('R exponent(T,h) and rational coefficients:')
for e,c in sorted(R.items()):print(e,c)
