"""Exact physical third jets of the normalized ruling forcing.

Reconstructs all coefficient lifts by a six-equation jet solve.  It does not
freeze the normalizing scales D/d or E/e while differentiating.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

ORDER=3
ZERO=(0,0,0)
class J:
 def __init__(self,c=0):
  self.c=({e:Q(v)for e,v in c.items()if v}if isinstance(c,dict)else({ZERO:Q(c)}if c else{}))
 @property
 def value(self):return self.c.get(ZERO,Q(0))
 def __add__(self,b):
  b=jet(b);o=dict(self.c)
  for e,v in b.c.items():
   o[e]=o.get(e,Q(0))+v
   if not o[e]:del o[e]
  return J(o)
 __radd__=__add__
 def __neg__(self):return J({e:-v for e,v in self.c.items()})
 def __sub__(self,b):return self+-jet(b)
 def __rsub__(self,b):return jet(b)+-self
 def __mul__(self,b):
  b=jet(b);o={}
  for e,v in self.c.items():
   for f,w in b.c.items():
    g=tuple(x+y for x,y in zip(e,f))
    if sum(g)<=ORDER:o[g]=o.get(g,Q(0))+v*w
  return J(o)
 __rmul__=__mul__
 def inverse(self):
  a=self.value;assert a
  n=(self-a)*(1/a)
  ans=J(0);power=J(1)
  for i in range(ORDER+1):ans+=((-1)**i)*power;power*=n
  return ans*(1/a)
 def __truediv__(self,b):return self*jet(b).inverse()
 def __rtruediv__(self,b):return jet(b)*self.inverse()
 def __pow__(self,n):
  assert isinstance(n,int)
  if n<0:return self.inverse()**(-n)
  ans=J(1);a=self
  while n:
   if n&1:ans*=a
   a*=a;n//=2
  return ans
 def partial(self,i):
  o={}
  for e,v in self.c.items():
   if e[i]:
    f=list(e);f[i]-=1;o[tuple(f)]=v*e[i]
  return J(o)
def jet(x):return x if isinstance(x,J)else J(x)
def var(x,i):
 e=[0,0,0];e[i]=1;return J({ZERO:Q(x),tuple(e):Q(1)})
def pow_unit(x,alpha):
 assert x.value==1
 ans=J(0);power=J(1);coef=Q(1)
 for n in range(ORDER+1):
  ans+=coef*power;power*=x-1;coef*=Q(alpha-n,n+1)
 return ans
def solve(matrix,rhs):
 n=len(rhs);a=[list(row)+[b]for row,b in zip(matrix,rhs)]
 for i in range(n):
  pivot=next(j for j in range(i,n)if a[j][i].value)
  a[i],a[pivot]=a[pivot],a[i]
  d=a[i][i];a[i]=[x/d for x in a[i]]
  for j in range(n):
   if j!=i:
    c=a[j][i];a[j]=[x-c*y for x,y in zip(a[j],a[i])]
 return [a[i][-1]for i in range(n)]
def action(v,f):return sum((v[i]*f.partial(i)for i in range(3)),J())

R,S,z=[var(1,i)for i in range(3)]
k=pow_unit(R*S,Q(1,6))
assert not(k**6-R*S).c
A=1+R;B=1+S;T=1+z**6;C=k/3;D=z*k/2;E=z/2
delta=3*R*S*z**6-3*R*S-8*R*z**6+R-S*z**6+2*S
H=64*pow_unit(T/2,Q(4,3))*pow_unit(A/2,Q(11,6))*pow_unit(B/2,Q(5,6))/(z*k*delta)
scaleS=2*pow_unit(T/2,Q(1,6))*pow_unit(A/2,Q(2,3))*pow_unit(B/2,Q(1,6))
scaleE=2*pow_unit(T/2,Q(2,3))*pow_unit(A/2,Q(1,6))*pow_unit(B/2,Q(1,6))
matrix=[
 [J(1),J(),J(),-A,2*A,2*A],
 [J(),J(1),J(),-B,-2*B,2*B],
 [C/(6*R),C/(6*S),J(),-C,J(),4*C/3],
 [D/(6*R),D/(6*S),D/z,-D,D,5*D/3],
 [J(),J(),J(Q(1,2)),-E,J(),2*E/3],
 [J(),J(),6*z**5,-T,J(),J()]]
VT=solve(matrix,[J(),J(),J(),J(),J(),J(1)])
VS=solve(matrix,[J(),J(),D/(2*A),J(1),J(),J()])
VE=solve(matrix,[J(),J(),J(),J(),J(1),J()])
inner=T*action(VT,H)-Q(4,3)*H
forcing=scaleS*action(VS,inner)
mixed=scaleE*action(VE,forcing)

# The normalized moduli are checked independently through full third jets.
c=Q(1,6)*k*pow_unit(T/2,Q(-1,3))*pow_unit(A/2,Q(-1,3))*pow_unit(B/2,Q(-1,3))
d=Q(1,4)*z*k*pow_unit(T/2,Q(-1,6))*pow_unit(A/2,Q(-2,3))*pow_unit(B/2,Q(-1,6))
e=Q(1,4)*z*pow_unit(T/2,Q(-2,3))*pow_unit(A/2,Q(-1,6))*pow_unit(B/2,Q(-1,6))
u=c-d*d/4
def up_to(f,n):return{a:b for a,b in f.c.items()if sum(a)<=n}
assert not up_to(action(VE,c),2)
assert not up_to(action(VE,d),2)
assert not up_to(scaleS*action(VS,u),2)
assert not up_to(scaleS*action(VS,d)-1,2)
assert not up_to(scaleE*action(VE,e)-1,2)
assert not up_to(T*action(VT,u)+u/3,2)
assert not up_to(T*action(VT,d)+d/6,2)
assert not up_to(T*action(VT,e)+2*e/3,2)
out={'arithmetic':'stdlib Fraction, total-order-three Taylor jets',
 'point':{'R':1,'S':1,'z':1,'k':1,'c':'1/6','d':'1/4','e':'1/4','u':'29/192'},
 'Hsrc':str(H.value),'T_minus_4over3_H':str(inner.value),
 'S_T_minus_4over3_H':str(forcing.value),
 'E_S_T_minus_4over3_H':str(mixed.value),
 'normalization_checks':8,
 'scope':'Exact local value for this source-directed annihilator channel; no global nonexistence or primitive claimed.'}
Path(__file__).with_name('reduced-mixed-derivative-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
