"""One source-driven genuine-horizontal construction with intrinsic scalar integration.
The horizontal currents solve H_a U+H_z W=−q^3/(6a^2) exactly.
No unrestricted existence/nonexistence claim is made by this calculation.
"""
import json
from pathlib import Path
import sympy as sp

MOD=1009
ORDER=7
class J:
 def __init__(self,x=0):
  self.v=([int(i)%MOD for i in x]+[0]*(ORDER+1))[:ORDER+1] if isinstance(x,list) else [int(x)%MOD]+[0]*ORDER
 def __add__(self,y):
  y=conv(y);return J([(a+b)%MOD for a,b in zip(self.v,y.v)])
 __radd__=__add__
 def __neg__(self):return J([-a for a in self.v])
 def __sub__(self,y):return self+-conv(y)
 def __rsub__(self,y):return conv(y)+-self
 def __mul__(self,y):
  y=conv(y);return J([sum(self.v[k]*y.v[n-k] for k in range(n+1))%MOD for n in range(ORDER+1)])
 __rmul__=__mul__
 def inv(self):
  if not self.v[0]:raise ZeroDivisionError
  out=[pow(self.v[0],-1,MOD)]
  for n in range(1,ORDER+1):out.append(-sum(self.v[k]*out[n-k] for k in range(1,n+1))*out[0]%MOD)
  return J(out)
 def __truediv__(self,y):return self*conv(y).inv()
 def __rtruediv__(self,y):return conv(y)*self.inv()
 def __pow__(self,n):
  if n<0:return self.inv()**(-n)
  out=J(1);b=self
  while n:
   if n&1:out=out*b
   b=b*b;n//=2
  return out
 def diff(self):return J([(n+1)*self.v[n+1] for n in range(ORDER)]+[0])
 def derivative(self,n):
  from math import factorial
  return self.v[n]*factorial(n)%MOD

def conv(x):return x if isinstance(x,J) else J(x)
Hsym,Csym=sp.symbols('H C')
raw=json.loads(Path('/workspace/off-paired-research-new/endpoint/reconstructed-connection.json').read_text())
matrices={s:[[sp.sympify(col[row],locals={'H':Hsym,'C':Csym}) for col in raw[s]['columns']] for row in range(4)] for s in ('H','C')}
def ev(expr,H,C):
 if expr==Hsym:return H
 if expr==Csym:return C
 if isinstance(expr,sp.Integer):return J(int(expr))
 if isinstance(expr,sp.Rational):return J(int(expr.p))/int(expr.q)
 if expr.is_Add:
  out=J(0)
  for x in expr.args:out+=ev(x,H,C)
  return out
 if expr.is_Mul:
  out=J(1)
  for x in expr.args:out*=ev(x,H,C)
  return out
 if expr.is_Pow:return ev(expr.args[0],H,C)**int(expr.args[1])
 raise ValueError(expr)
def mv(M,v):return [sum((M[i][j]*v[j] for j in range(4)),J(0)) for i in range(4)]
def solve_jets(M,b):
 A=[row[:]+[bb] for row,bb in zip(M,b)]
 for j in range(4):
  k=next(k for k in range(j,4) if A[k][j].v[0]);A[j],A[k]=A[k],A[j]
  inv=A[j][j].inv();A[j]=[x*inv for x in A[j]]
  for k in range(4):
   if k==j:continue
   t=A[k][j];A[k]=[x-t*y for x,y in zip(A[k],A[j])]
 return [A[i][4] for i in range(4)]

def source_guided_currents(a,C,z):
 q=3*C-J(3)/2*a*z
 K=3*a*z+12*z**5
 M=-18*a**3+54*a*z**6
 E=J(1)/2-9*(K**4-3*K*K*M+M*M)/a
 FF=6*z**5-J(3)/4*a*z-9*(K**3*M-2*K*M*M)/a
 Res=FF*FF-K*E*FF+M*E*E
 w1=(-FF*(K*K-M)+K*M*E)/(6*a*a*Res)
 w0=M*(E*M-K*FF)/(6*a*a*Res)
 Wb=w1*q+w0
 J5=-9/a*(q**3-K*q*q+(K*K-M)*q-K**3+2*K*M)
 V=(K-q)/(6*a*a)-E*w1-J5*Wb
 L=z/a+2*q/(9*a*a)
 U=-9*a*a*V
 W=Wb+9*a*a*L*V
 Ha=2*a-2*q**6/a**3-9*z*q**5/a**2-J(3)/4*z*z
 Hz=6*z**5+q/2-J(3)/4*a*z-9*q**5/a
 assert (Ha*U+Hz*W+q**3/(6*a*a)).v[0]==0
 return U,W

def horizontal_divergence(c0):
 Ua=source_guided_currents(J([1,1]),J(c0),J(1))[0].derivative(1)
 Wz=source_guided_currents(J(1),J(c0),J([1,1]))[1].derivative(1)
 return (Ua+Wz)%MOD

def operator_at(c0):
 C=J([c0,1]);q=3*C-J(3)/2
 H=1+q**6+1+q/2 # a=z=1: H=a²+q6/a²+z6+qz/2+1 =3+q6+q/2
 H=3+q**6+q/2
 h=18*q**5+J(3)/2
 MH=[[ev(x,H,C) for x in row] for row in matrices['H']]
 MC=[[ev(x,H,C) for x in row] for row in matrices['C']]
 N=[[MC[i][j]+h*MH[i][j] for j in range(4)] for i in range(4)]
 cols=[[J(1),J(0),J(0),J(0)]]
 for _ in range(4):
  last=cols[-1];prod=mv(N,last)
  cols.append([x.diff()+y for x,y in zip(last,prod)])
 ds=solve_jets([[cols[j][i] for j in range(4)] for i in range(4)],cols[4])
 Nr=3*H-2*C*h
 den=C*Nr**3
 gs=[C**k/den for k in range(39)]
 def adj(g):return (g.derivative(4)+(ds[3]*g).derivative(3)-(ds[2]*g).derivative(2)+(ds[1]*g).derivative(1)-(ds[0]*g).v[0])%MOD
 # Equation +Lhat_delta* G0 = +C/9 delta[q³/(a²rH)] = C/3 delta[q³/Nr].
 forcing=horizontal_divergence(c0)
 return [adj(g) for g in gs],forcing

def linear_solve(rows,n):
 piv={};inconsistent=False
 for row0 in rows:
  row=row0[:]
  for j,pr in sorted(piv.items()):
   if row[j]:
    t=row[j];row=[(x-t*y)%MOD for x,y in zip(row,pr)]
  nz=next((j for j in range(n) if row[j]),None)
  if nz is None:
   if row[-1]:inconsistent=True;break
   continue
  inv=pow(row[nz],-1,MOD);row=[x*inv%MOD for x in row];piv[nz]=row
 if inconsistent:return None,len(piv)
 sol=[0]*n
 for j in sorted(piv,reverse=True):sol[j]=(piv[j][-1]-sum(piv[j][k]*sol[k] for k in range(j+1,n)))%MOD
 return sol,len(piv)

rows=[];points=[]
for c in range(1,90):
 try:row,rhs=operator_at(c)
 except (ZeroDivisionError,StopIteration):continue
 rows.append(row+[rhs]);points.append(c)
 if len(rows)>=48:break
sol,rank=linear_solve(rows,39)
out={'modulus':MOD,'parameters':{'a':1,'z':1},'pole_bound':'D=C*(3H-2C H_C)^3','numerator_degree_bound':38,'points':points,'rank':rank,'solution':sol,'scope':'Source-guided genuine horizontal Bezout currents fixed; generic (a,z) lift and original-source verification required.'}
Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/source-guided-horizontal-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('points',len(points),'rank',rank,'consistent',sol is not None,flush=True)
if sol is not None:
 for c in range(101,113):
  try:row,rhs=operator_at(c)
  except (ZeroDivisionError,StopIteration):continue
  assert sum(x*y for x,y in zip(row,sol))%MOD==rhs
 print('12 fresh scalar operator evaluations passed')
