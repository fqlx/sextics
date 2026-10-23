"""Exact physical source field used by the two-cotangent current.

This module contains only verbatim arithmetic/source-definition slices, plus
namespace/context bindings. It does not execute or claim any failed candidate.
See native_source_field.provenance.json for exact source hashes and boundaries.
"""
import flint
CTX=flint.fmpq_mpoly_ctx.get(['R','D','a','m'])

class RF:
 def __init__(self,n=0,d=1):
  if isinstance(n,RF):self.n,self.d=n.n,n.d;return
  self.n=n if isinstance(n,flint.fmpq_mpoly)else CTX.constant(n)
  self.d=d if isinstance(d,flint.fmpq_mpoly)else CTX.constant(d)
  if not self.d:raise ZeroDivisionError
  if not self.n:self.d=CTX.constant(1);return
  g=self.n.gcd(self.d);self.n=self.n//g;self.d=self.d//g
  # Polynomial gcds are monic over QQ and do not remove a common scalar.
  # Normalize that scalar as well, preventing arithmetic-equivalent fractions
  # from accumulating thousands of digits in both numerator and denominator.
  lc=self.d.leading_coefficient();self.n=self.n/lc;self.d=self.d/lc
 def __add__(self,o):
  o=RF(o);g=self.d.gcd(o.d);ad=self.d//g;bd=o.d//g
  return RF(self.n*bd+o.n*ad,ad*o.d)
 __radd__=__add__
 def __neg__(self):return RF(-self.n,self.d)
 def __sub__(self,o):return self+-RF(o)
 def __rsub__(self,o):return RF(o)+-self
 def __mul__(self,o):
  o=RF(o);g=self.n.gcd(o.d);h=o.n.gcd(self.d)
  return RF((self.n//g)*(o.n//h),(self.d//h)*(o.d//g))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=RF(o)
  if not o.n:raise ZeroDivisionError
  return self*RF(o.d,o.n)
 def __rtruediv__(self,o):return RF(o)/self
 def __pow__(self,k):return RF(self.n**k,self.d**k)if k>=0 else RF(self.d**(-k),self.n**(-k))
 def diff(self,i):return RF(self.n.derivative(i)*self.d-self.n*self.d.derivative(i),self.d*self.d)
 def __eq__(self,o):
  o=RF(o);return self.n*o.d==o.n*self.d
 def __bool__(self):return bool(self.n)
 def info(self):return {'numerator_terms':len(self.n),'denominator_terms':len(self.d),'numerator_degree':int(self.n.total_degree()),'denominator_degree':int(self.d.total_degree())}
 def at(self,p):return self.n(*p)/self.d(*p)


R,D,a,m=map(RF,CTX.gens());Z=4*R+R*R/(4*D)

class E2:
 def __init__(self,x=0,y=0):
  if isinstance(x,E2):self.x,self.y=x.x,x.y
  else:self.x,self.y=RF(x),RF(y)
 def __add__(self,o):o=E2(o);return E2(self.x+o.x,self.y+o.y)
 __radd__=__add__
 def __neg__(self):return E2(-self.x,-self.y)
 def __sub__(self,o):return self+-E2(o)
 def __rsub__(self,o):return E2(o)+-self
 def __mul__(self,o):o=E2(o);return E2(self.x*o.x+self.y*o.y*Z,self.x*o.y+self.y*o.x)
 __rmul__=__mul__
 def inv(self):d=self.x*self.x-self.y*self.y*Z;return E2(self.x/d,-self.y/d)
 def __truediv__(self,o):return self*E2(o).inv()
 def __rtruediv__(self,o):return E2(o)*self.inv()
 def __pow__(self,n):
  if n<0:return self.inv()**(-n)
  ans=E2(1);p=self
  while n:
   if n&1:ans=ans*p
   p=p*p;n//=2
  return ans
 def diff(self,i):return E2(self.x.diff(i),self.y.diff(i)+self.y*Z.diff(i)/(2*Z))
 def __bool__(self):return bool(self.x)or bool(self.y)
 def __eq__(self,o):o=E2(o);return self.x==o.x and self.y==o.y
 def info(self):return {'even':self.x.info(),'Vodd':self.y.info()}
 def at(self,pt,v):return self.x.at(pt)+v*self.y.at(pt)
 def data(self):return {'even_numerator':str(self.x.n),'even_denominator':str(self.x.d),'Vodd_numerator':str(self.y.n),'Vodd_denominator':str(self.y.d)}


V=E2(0,1)
A=(R**3+1)/R;kS=R*R/(R**3+1)
L=D+a/3-a*a/(12*A)
M=-E2(a*L/(6*A))-(V+1/(216*A*A))*a**3


def B(z):return E2(z).diff(0)+E2(D/R)*E2(z).diff(1)
LR=B(L)-kS*L;La=L.diff(2)
MR=B(M)-M/(2*R);Ma=M.diff(2)
K=Ma*LR-E2(La)*MR
LD=-a/(3*A)
MD=-D/(3*A)-a/(9*A)+a*a/(18*A*A)
Kd=E2(MD.diff(2))*LR+Ma*(B(LD)-kS*LD)-E2(LD.diff(2))*MR-E2(La)*(B(MD)-MD/(2*R))
vR=(E2(LD)*Ma-E2(La)*MD)/K
va=(LR*MD-MR*LD)/K
f0=E2(D/(18*R))/K # 1/(72*y²*K),actualy²=R/(4D)
rho=E2(D/(18*R))*(vR*B(K)+va*K.diff(2)-Kd)/(K*K)


S3=R**3+1

class W:
 def __init__(self,z=0,ar=0,bs=0):
  if isinstance(z,W):self.z,self.ar,self.bs=z.z,z.ar,z.bs;return
  q,ar=divmod(ar,2);t,bs=divmod(bs,3)
  self.z=E2(z)*R**q*S3**t;self.ar,self.bs=ar,bs
 def __bool__(self):return bool(self.z)
 def __neg__(self):return W(-self.z,self.ar,self.bs)
 def __add__(self,o):
  o=W(o)
  if not self:return o
  if not o:return self
  assert(self.ar,self.bs)==(o.ar,o.bs),((self.ar,self.bs),(o.ar,o.bs))
  return W(self.z+o.z,self.ar,self.bs)
 __radd__=__add__
 def __sub__(self,o):return self+-W(o)
 def __rsub__(self,o):return W(o)+-self
 def __mul__(self,o):o=W(o);return W(self.z*o.z,self.ar+o.ar,self.bs+o.bs)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=W(o);return W(self.z/o.z,self.ar-o.ar,self.bs-o.bs)
 def __rtruediv__(self,o):return W(o)/self
 def __pow__(self,n):return W(self.z**n,self.ar*n,self.bs*n)
 def Bcoef(self):return B(self.z)+self.z*(self.ar/(2*R)+self.bs*kS)
 def da(self):return W(self.z.diff(2),self.ar,self.bs)
 def dl(self):return W((Ma*self.Bcoef()-MR*self.z.diff(2))/K,self.ar,self.bs+1)
 def dm(self):return W((-E2(La)*self.Bcoef()+LR*self.z.diff(2))/K,self.ar+1,self.bs)
 def e(self):return 2*W(L,0,-1)*self.dl()+3*W(M,-1,0)*self.dm()
 def l0(self):return 3*self.dl().dl()+W(L,0,-1)*self.dm().dm()
 def l2star(self):return self.e().e()+12*self.e()+36*self-36*self.dm().dm()
 def data(self):return {'r_power':self.ar,'S_power':self.bs,'coefficient':self.z.data()}


# Preserve the exact constructor/auditor nested-source namespace API.
ns=globals()
