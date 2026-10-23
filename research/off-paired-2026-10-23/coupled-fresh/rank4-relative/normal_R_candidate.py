"""One source-derived candidate, actual physical derivatives, exact Fraction jets."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
NORDER=4
class J:
 def __init__(self,x=0):
  self.a=([F(t) for t in x]+[F(0)]*(NORDER+1))[:NORDER+1] if isinstance(x,list) else [F(x)]+[F(0)]*NORDER
 def __add__(self,y):
  y=conv(y);return J([a+b for a,b in zip(self.a,y.a)])
 __radd__=__add__
 def __neg__(self):return J([-x for x in self.a])
 def __sub__(self,y):return self+-conv(y)
 def __rsub__(self,y):return conv(y)+-self
 def __mul__(self,y):
  y=conv(y);return J([sum(self.a[k]*y.a[n-k] for k in range(n+1)) for n in range(NORDER+1)])
 __rmul__=__mul__
 def inv(self):
  assert self.a[0];out=[1/self.a[0]]
  for n in range(1,NORDER+1):out.append(-sum(self.a[k]*out[n-k] for k in range(1,n+1))/self.a[0])
  return J(out)
 def __truediv__(self,y):return self*conv(y).inv()
 def __rtruediv__(self,y):return conv(y)*self.inv()
 def __pow__(self,n):
  if n<0:return self.inv()**(-n)
  out=J(1);b=self
  while n:
   if n%2:out=out*b
   b=b*b;n//=2
  return out
 def d(self,n):return self.a[n]*factorial(n)
def conv(x):return x if isinstance(x,J) else J(x)
def data(a,H,C,z):
 q=3*C-F(3,2)*a*z;qa=-F(3,2)*z
 M=z**6+q*z/2+1-H
 P=a**4+q**6+a*a*M
 Pa=4*a**3+6*q**5*qa+2*a*M+a*a*qa*z/2
 Paa=12*a*a+30*q**4*qa*qa+2*M+4*a*qa*z/2
 PC=18*q**5+F(3,2)*a*a*z
 Delta=4*C**6-729*H**4
 R=-27*C**3/a+F(81,4)*C*z*z*a-F(27,16)*z**3*a*a
 Ra=27*C**3/(a*a)+F(81,4)*C*z*z-F(27,8)*z**3*a
 f=Delta*R/C;fa=Delta*Ra/C
 NN=a*a-2*C*PC/(3*H)
 U=3*PC**4*Paa**2*fa/(NN*Pa**5)
 phiH=((2*a*q**3+3*a*a*q*q*qa)*Pa-a*a*q**3*Paa)/Pa**3
 cs=[-55*C*C/Delta,-309*C**3/Delta,-(271*C**6-1458*H**4)/(C*C*Delta),-2*(32*C**6+729*H**4)/(C*Delta)]
 return dict(P=P,Pa=Pa,Paa=Paa,PC=PC,N=NN,f=f,U=U,phiH=phiH,cs=cs)
a0=C0=z0=F(1);q0=3*C0-F(3,2)*a0*z0
H0=a0*a0+q0**6/(a0*a0)+z0**6+q0*z0/2+1
C=J([C0,1]);H=J(H0);z=J(z0);a=J(a0)
# Implicit Newton in the truncated jet ring gives actual C derivatives at fixed H,z.
for _ in range(4):
 d=data(a,H,C,z);a=a-d['P']/d['Pa']
d=data(a,H,C,z)
assert d['P'].a==[0]*(NORDER+1)
f=d['f'];cs=d['cs']
Lstar=f.d(4)+(cs[3]*f).d(3)-(cs[2]*f).d(2)+(cs[1]*f).d(1)-(cs[0]*f).d(0)
base=data(J(a0),J(H0),J(C0),J(z0))
Pa0,NN0=base['Pa'].a[0],base['N'].a[0]
# First-order T jet, including the physical a component.
dt=data(J([a0,NN0/Pa0]),J([H0,1]),J([C0,2*C0/(3*H0)]),J(z0))
TU=dt['U'].d(1)
sigma=base['phiH'].a[0]/6
# For f=Delta R/C and U=leading critical correction, W=0.
residual=sigma+Lstar-TU
assert residual
out={'candidate':'f=Delta R/C; U=3 PC^4 Paa^2 f_a/(N Pa^5); W=0',
     'point':{'a':str(a0),'H':str(H0),'C':str(C0),'z':str(z0)},
     'sigma':str(sigma),'Lstar_f':str(Lstar),'T_U':str(TU),'residual_sigma_plus_Lstar_minus_TU':str(residual),
     'claim':'One exact residual evaluation; candidate does not yet solve. No search or nonexistence claim.'}
Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/normal-R-candidate-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('Actual derivative jets passed; explicit candidate residual is nonzero at a=C=z=1, H=969/64.')
print('Residual numerator digits:',len(str(abs(residual.numerator))))
