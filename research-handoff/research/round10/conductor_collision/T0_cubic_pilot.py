"""Finite-prime cubic initial model at the exceptional T0 collision.
Actual F is used to eliminate v, and S=b*eta after conductor blowup.
"""
from pathlib import Path
import pickle,json,itertools,math
import sympy as sy
from flint import nmod_poly
H=Path(__file__).parent;p=1000393;N=3;zero=(0,)*4
class J:
 def __init__(self,d=0):self.d={zero:int(d)%p}if not isinstance(d,dict)else{k:v%p for k,v in d.items()if v%p}
 def __add__(self,o):
  o=o if isinstance(o,J)else J(o);d=self.d.copy()
  for k,v in o.d.items():d[k]=(d.get(k,0)+v)%p
  return J(d)
 __radd__=__add__
 def __neg__(self):return J({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-o if isinstance(o,J)else self+(-o)
 def __rsub__(self,o):return -self+o
 def __mul__(self,o):
  o=o if isinstance(o,J)else J(o);d={}
  for k,v in self.d.items():
   for l,w in o.d.items():
    z=tuple(a+b for a,b in zip(k,l))
    if sum(z)<=N:d[z]=(d.get(z,0)+v*w)%p
  return J(d)
 __rmul__=__mul__
 def __pow__(self,k):
  r=J(1);a=self
  while k:
   if k%2:r=r*a
   a=a*a;k//=2
  return r
 def root6(self,c):
  assert self.d.get(zero,0)==0
  out=J(1);coef=1;pw=J(1)
  for i in range(1,N+1):
   coef=coef*((1-(i-1)*6)%p)*pow(6*i,-1,p)%p;pw=pw*self;out=out+coef*pw
  return c*out

def rat(c):return int(c.p)%p*pow(int(c.q),-1,p)%p
roots=lambda f:[(-int(g[0])*pow(int(g[1]),-1,p))%p for g,e in f.factor()[1]if g.degree()==1]
aa=roots(nmod_poly([1]+[0]*5+[1],p));vv=roots(nmod_poly([171*pow(196,-1,p)%p]+[0]*5+[1],p))
for a0,v0 in itertools.product(aa,vv):
 E=-(9*a0*v0-5)*pow(28*a0,-1,p)%p
 ee=roots(nmod_poly([-E,0,1],p))
 if ee:e0=ee[0];break
else:raise RuntimeError('no split point')
c=5*pow(7,-1,p)%p
De,Z,B,Et=[J({tuple(int(i==j)for i in range(4)):1})for j in range(4)]
S=B*Et;a=(-S).root6(a0);e=De+e0
T=J(0)
for _ in range(5):
 v=(-pow(171,-1,p)*T).root6(v0)
 T=-196*(Z*Z+c*e**2*B*(v*a+(-c*pow(2,-1,p)+Z)*(1+a*v))+c*e**4*(a*B+v*B**3)+e**6*(S+B**6))
v=(-pow(171,-1,p)*T).root6(v0)
d=pickle.load(open(H/'strict_normalization.pickle','rb'));asym,bsym,tsym,vsym,_=d['variables'];ap=[a**i for i in range(20)];bp=[B**i for i in range(15)];vp=[v**i for i in range(20)]
def evaluate(f):
 out=J(0)
 for (i,j,k,l),cc in sy.Poly(f,asym,bsym,tsym,vsym).terms():out=out+rat(cc)*ap[i]*bp[j]*vp[l]
 return out
q,r,s=[evaluate(d['parts'][13][i])+e**2*evaluate(d['parts'][15][i])for i in range(3)]
g=q*Et**2+r*Et+s
low={k:v for k,v in g.d.items()if sum(k)<3};assert not low,low
syms=sy.symbols('de z b eta');expr=sum(v*sy.prod(x**j for x,j in zip(syms,k))for k,v in g.d.items())
res=dict(prime=p,a0=a0,v0=v0,e0=e0,E=E,initialDegree=3,cubic=str(expr),terms={','.join(map(str,k)):v for k,v in g.d.items()},allLowerCoefficientsZero=True,scope='Finite-prime pilot of exact actual local jet construction; characteristic-zero singularity type not concluded.')
(H/'T0_cubic_pilot.json').write_text(json.dumps(res,indent=2)+'\n');(H/'T0_cubic_pilot.sing').write_text('ring R='+str(p)+',('+','.join(map(str,syms))+'),dp;\npoly f='+str(expr).replace('**','^')+';\nprint(factorize(f));\nideal J=diff(f,de),diff(f,z),diff(f,b),diff(f,eta);\nprint(std(J));\nprint(dim(std(J)));\nquit;\n')
print(json.dumps(res,indent=2))
