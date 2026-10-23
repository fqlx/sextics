"""Exact physical point evaluation of the retained infinity remainder."""
from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path
N=7
class J:
 def __init__(self,x=0): self.c=(list(x)+[F(0)]*(N+1))[:N+1] if isinstance(x,(list,tuple)) else [F(x)]+[F(0)]*N
 def __add__(self,b):
  b=b if isinstance(b,J) else J(b);return J([x+y for x,y in zip(self.c,b.c)])
 __radd__=__add__
 def __neg__(self):return J([-x for x in self.c])
 def __sub__(self,b):return self+-b if isinstance(b,J) else self+-J(b)
 def __rsub__(self,b):return J(b)+-self
 def __mul__(self,b):
  b=b if isinstance(b,J) else J(b);return J([sum(self.c[k]*b.c[n-k] for k in range(n+1)) for n in range(N+1)])
 __rmul__=__mul__
 def inv(self):
  cc=[1/self.c[0]]
  for n in range(1,N+1):cc.append(-sum(self.c[k]*cc[n-k] for k in range(1,n+1))/self.c[0])
  return J(cc)
 def __truediv__(self,b):return self*(b if isinstance(b,J) else J(b)).inv()
 def __rtruediv__(self,b):return J(b)*self.inv()
 def __pow__(self,n):
  if n<0:return self.inv()**(-n)
  r=J(1)
  for _ in range(n):r=r*self
  return r
 def d(self):return J([(i+1)*self.c[i+1] for i in range(N)]+[F(0)])
C=J([F(1),F(1)]);z=F(1);H=F(969,64);a=J(1)
def P(a):
 q=3*C-F(3,2)*a*z
 return a**4+q**6+a*a*(z**6+q*z/2+1-H)
def Pa(a):
 q=3*C-F(3,2)*a*z
 return 4*a**3-9*z*q**5+2*a*(z**6+q*z/2+1-H)-F(3,4)*a*a*z*z
for _ in range(4):a=a-P(a)/Pa(a)
assert all(x==0 for x in P(a).c)
def theta(x):return C*x.d()
def B(f):
 g=theta(theta(f))-3*theta(f)+2*f;g=2*theta(g)+3*g
 return (C**3*(44*theta(theta(g))-35*g)/H**2-729*H**2*(11*theta(theta(g))-39*g)/C**3)/630
u=a-1;l=J(0)
for j in range(1,N+1):l=l+(-1)**(j+1)*u**j/j
R=-27*C**3/a+F(81,4)*C*z*z*a-F(27,16)*z**3*a*a
k=F(81,2)*C*C*z
S=(B(theta(2*theta(R-k*l)-3*(R-k*l)))/(27*H**2)).c[0]
assert S!=0
out={'point':{'a':'1','C':'1','z':'1','H':'969/64'},'S':str(S),'S_nonzero':S!=0,'certificate':False}
Path(__file__).with_name('two-normal-remainder-point.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
