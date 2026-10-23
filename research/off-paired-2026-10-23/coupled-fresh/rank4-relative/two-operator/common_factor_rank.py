"""Positive common-factor closure via the fixed 15-dimensional order-four space."""
import sympy as s,json,math
from pathlib import Path
PPRIME=1009;ORDER=10
class J:
 def __init__(self,v=0):self.a=(([int(x)%PPRIME for x in v]+[0]*ORDER)[:ORDER+1] if isinstance(v,list) else [int(v)%PPRIME]+[0]*ORDER)
 def __add__(self,b):b=asj(b);return J([(x+y)%PPRIME for x,y in zip(self.a,b.a)])
 __radd__=__add__
 def __neg__(self):return J([-x for x in self.a])
 def __sub__(self,b):return self+-asj(b)
 def __rsub__(self,b):return asj(b)+-self
 def __mul__(self,b):
  b=asj(b);return J([sum(self.a[k]*b.a[n-k]for k in range(n+1))%PPRIME for n in range(ORDER+1)])
 __rmul__=__mul__
 def inv(self):
  assert self.a[0];out=[pow(self.a[0],-1,PPRIME)]
  for n in range(1,ORDER+1):out.append(-sum(self.a[k]*out[n-k]for k in range(1,n+1))*out[0]%PPRIME)
  return J(out)
 def __truediv__(self,b):return self*asj(b).inv()
 def __rtruediv__(self,b):return asj(b)*self.inv()
 def __pow__(self,n):
  if n<0:return self.inv()**(-n)
  out=J(1);b=self
  while n:
   if n&1:out=out*b
   b=b*b;n//=2
  return out
 def __bool__(self):return any(self.a)
def asj(v):return v if isinstance(v,J)else J(v)
def rat(q):
 n,d=s.fraction(s.cancel(q));return int(n)%PPRIME*pow(int(d)%PPRIME,-1,PPRIME)%PPRIME
H,C=s.symbols('H C');h=s.symbols('h0:4')
data=json.loads(Path('/workspace/off-paired-research-new/endpoint/reconstructed-connection.json').read_text())
def mat(k):return s.Matrix([[s.sympify(x,locals={'H':H,'C':C})for x in col]for col in data[k]['columns']]).T
MH,MC=mat('H'),mat('C')
e=s.Matrix([1,0,0,0]);mon=[(i,j)for n in range(5)for i in range(n+1)for j in [n-i]]
image={(0,0):e}
for n in range(1,5):
 for i,j in [x for x in mon if sum(x)==n]:
  if i: v=image[i-1,j];image[i,j]=(v.diff(H)+MH*v).applyfunc(s.cancel)
  else:v=image[i,j-1];image[i,j]=(v.diff(C)+MC*v).applyfunc(s.cancel)
point={H:s.Rational(969,64),C:1}
M=[[rat(image[m][row].subs(point))for m in mon]for row in range(4)]
print('universal image matrix ready',flush=True)
# Formal delta powers in the commuting universal D_H,D_C monomials.
Ds=[{(0,0):s.Integer(1)}]
for n in range(4):
 nxt={}
 def put(m,x):nxt[m]=s.expand(nxt.get(m,0)+x)
 for (i,j),v in Ds[-1].items():
  dv=sum(s.diff(v,h[k])*h[k+1]for k in range(3))
  put((i,j),dv);put((i,j+1),v);put((i+1,j),h[0]*v)
 Ds.append({m:v for m,v in nxt.items()if v!=0})
# Actual fixed-H,C z jet: P(a,H,C,z)=0.
a=J(1);z=J([1,1]);HH=J(rat(point[H]));CC=J(1)
for it in range(4):
 q=3*CC-J(3)/2*a*z
 PP=a**4+q**6+a*a*(z**6+q*z/2+1-HH)
 Pa=4*a**3-9*z*q**5+2*a*(z**6+q*z/2+1-HH)-J(3)/4*a*a*z*z
 a=a-PP/Pa
q=3*CC-J(3)/2*a*z
assert not (a**4+q**6+a*a*(z**6+q*z/2+1-HH))
hv=[18*q**5/a**2+J(3)/2*z,270*q**4/a**2,3240*q**3/a**2,29160*q**2/a**2]
def ev(poly):
 out=J(0)
 for exps,co in s.Poly(poly,*h).terms():
  t=J(rat(co))
  for x,n in zip(hv,exps):t=t*x**n
  out=out+t
 return out
op=[[ev(Ds[n].get(m,0))for m in mon]for n in range(5)]
cols=[[sum((op[n][k]*M[row][k]for k in range(15)),J(0))for row in range(4)]for n in range(5)]
# Solve the cyclic 4x4 system over the exact truncated finite-field jet ring.
A=[[cols[col][row]for col in range(4)]+[cols[4][row]]for row in range(4)]
for c in range(4):
 k=next(r for r in range(c,4)if A[r][c].a[0]);A[c],A[k]=A[k],A[c]
 den=A[c][c];A[c]=[x/den for x in A[c]]
 for r in range(4):
  if r!=c:
   v=A[r][c];A[r]=[x-v*y for x,y in zip(A[r],A[c])]
d=[A[j][4]for j in range(4)]
vec=[op[4][k]-sum((d[j]*op[j][k]for j in range(4)),J(0))for k in range(15)]
# All coefficients and image reductions are exact modulo p, with every pivot unit.
rows=[[math.factorial(n)%PPRIME*v.a[n]%PPRIME for v in vec]for n in range(ORDER+1)]
for row in rows:assert all(sum(M[i][k]*row[k]for k in range(15))%PPRIME==0 for i in range(4))
basis=[];piv=[];indices=[]
for idx,row in enumerate(rows):
 v=row[:]
 for b,p in zip(basis,piv):
  fac=v[p]
  if fac:v=[(x-fac*y)%PPRIME for x,y in zip(v,b)]
 if any(v):
  p=next(k for k,x in enumerate(v)if x);den=pow(v[p],-1,PPRIME);v=[x*den%PPRIME for x in v]
  basis.append(v);piv.append(p);indices.append(idx)
  print('closure rank',len(basis),'at derivative',idx,flush=True)
 if len(basis)==11:break
out={'prime':PPRIME,'point':{'a':1,'C':1,'z':1,'H':'969/64'},'monomials_DH_DC':mon,'universal_image_matrix_mod_p':M,
'coefficient_derivative_rows_mod_p':rows,'rank':len(basis),'independent_derivative_indices':indices,'pivot_monomial_indices':piv,
'claim':'Positive common-factor span certificate if rank=11; no exclusion if smaller.'}
Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/two-operator/common-factor-rank-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('FINAL RANK',len(basis),flush=True)
