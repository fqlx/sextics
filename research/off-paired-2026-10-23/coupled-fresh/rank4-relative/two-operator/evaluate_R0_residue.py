"""Actual mixed C/a/z jets for source-carrying R0 interpolation residue.
No assertion of a primitive. All field arithmetic is exact modulo a prime.
"""
import json
import os
from pathlib import Path
import sympy as sp
PRIME=1009
CMAX=int(os.environ.get('R0_CMAX','7'))
PMAX=int(os.environ.get('R0_PMAX','2'))
indices=sorted([(c,a,z)for c in range(CMAX+1)for a in range(PMAX+1)for z in range(PMAX+1-a)],key=lambda t:(sum(t),t))
lookup={t:i for i,t in enumerate(indices)}; ZERO=lookup[(0,0,0)]
conv_pairs=[[]for _ in indices]
for i,x in enumerate(indices):
 for j,y in enumerate(indices):
  t=tuple(xx+yy for xx,yy in zip(x,y))
  if t in lookup:conv_pairs[lookup[t]].append((i,j))
inv_pairs=[[(i,j)for i,j in pairs if i!=ZERO]for pairs in conv_pairs]
class J:
 def __init__(self,x=0,raw=False):
  self.v=[int(a)%PRIME for a in x] if raw else [0]*len(indices)
  if not raw:self.v[ZERO]=int(x)%PRIME
 @classmethod
 def var(cls,value,direction):
  v=cls(value);key=[0,0,0];key[direction]=1;v.v[lookup[tuple(key)]]=1;return v
 def __add__(self,y):
  y=asj(y);return J([(x+y)%PRIME for x,y in zip(self.v,y.v)],True)
 __radd__=__add__
 def __neg__(self):return J([-x for x in self.v],True)
 def __sub__(self,y):return self+-asj(y)
 def __rsub__(self,y):return asj(y)+-self
 def __mul__(self,y):
  y=asj(y);return J([sum(self.v[i]*y.v[j]for i,j in pairs)%PRIME for pairs in conv_pairs],True)
 __rmul__=__mul__
 def inv(self):
  if self.v[ZERO]==0:raise ZeroDivisionError
  out=[0]*len(indices);out[ZERO]=pow(self.v[ZERO],-1,PRIME)
  for k in range(1,len(indices)):
   out[k]=-out[ZERO]*sum(self.v[i]*out[j]for i,j in inv_pairs[k])%PRIME
  return J(out,True)
 def __truediv__(self,y):return self*asj(y).inv()
 def __rtruediv__(self,y):return asj(y)*self.inv()
 def __pow__(self,n):
  if n<0:return self.inv()**(-n)
  ans=J(1);b=self
  while n:
   if n&1:ans=ans*b
   b=b*b;n//=2
  return ans
 def diff(self,direction=0):
  out=[]
  for t in indices:
   tt=list(t);tt[direction]+=1
   out.append(self.v[lookup[tuple(tt)]]*tt[direction]if tuple(tt)in lookup else 0)
  return J(out,True)
 def const(self):return self.v[ZERO]
def asj(x):return x if isinstance(x,J)else J(x)
def source_data(a,C,z):
 q=3*C-J(3)/2*a*z
 H=a*a+q**6/(a*a)+z**6+q*z/2+1
 Ha=2*a-2*q**6/a**3-9*z*q**5/a**2-J(3)/4*z*z
 Hz=6*z**5+q/2-J(3)/4*a*z-9*q**5/a
 h=18*q**5/a**2+J(3)/2*z
 K=3*a*z+12*z**5;M=-18*a**3+54*a*z**6
 E=J(1)/2-9*(K**4-3*K*K*M+M*M)/a
 FF=6*z**5-J(3)/4*a*z-9*(K**3*M-2*K*M*M)/a
 R=FF*FF-K*E*FF+M*E*E
 w1num=(-FF*(K*K-M)+K*M*E)/(6*a*a)
 w0num=M*(E*M-K*FF)/(6*a*a)
 Wbnum=w1num*q+w0num
 J5=-9/a*(q**3-K*q*q+(K*K-M)*q-K**3+2*K*M)
 Vnum=R*(K-q)/(6*a*a)-E*w1num-J5*Wbnum
 L=z/a+2*q/(9*a*a)
 Unum=-9*a*a*Vnum;Wnum=Wbnum+9*a*a*L*Vnum
 Dnum=R*(Unum.diff(1)+Wnum.diff(2))-Unum*R.diff(1)-Wnum*R.diff(2)
 A=Hz*R.diff(1)-Ha*R.diff(2)
 return locals()
Hsym,Csym=sp.symbols('H C')
raw=json.loads(Path('/workspace/off-paired-research-new/endpoint/reconstructed-connection.json').read_text())
matrices={s:[[sp.sympify(col[row],locals={'H':Hsym,'C':Csym})for col in raw[s]['columns']]for row in range(4)]for s in('H','C')}
def matrix_jets(H,C,h):
 cache={}
 def ev(e):
  if e in cache:return cache[e]
  if e==Hsym:v=H
  elif e==Csym:v=C
  elif isinstance(e,sp.Integer):v=J(int(e))
  elif isinstance(e,sp.Rational):v=J(int(e.p))/int(e.q)
  elif e.is_Add:
   v=J(0)
   for t in e.args:v+=ev(t)
  elif e.is_Mul:
   v=J(1)
   for t in e.args:v*=ev(t)
  elif e.is_Pow:v=ev(e.args[0])**int(e.args[1])
  else:raise ValueError(e)
  cache[e]=v;return v
 return [[ev(matrices['C'][i][j])+h*ev(matrices['H'][i][j])for j in range(4)]for i in range(4)]
def monic_coeffs(d):
 N=matrix_jets(d['H'],d['C'],d['h'])
 cols=[[J(1),J(0),J(0),J(0)]]
 for _ in range(4):
  v=cols[-1];cols.append([v[i].diff()+sum((N[i][j]*v[j]for j in range(4)),J(0))for i in range(4)])
 A=[[cols[j][i]for j in range(4)]+[cols[4][i]]for i in range(4)]
 for j in range(4):
  k=next(k for k in range(j,4)if A[k][j].const());A[j],A[k]=A[k],A[j]
  inverse=A[j][j].inv();A[j]=[x*inverse for x in A[j]]
  for k in range(4):
   if k==j:continue
   t=A[k][j];A[k]=[x-t*y for x,y in zip(A[k],A[j])]
 return [A[i][4]for i in range(4)]
def diffn(f,n):
 for _ in range(n):f=f.diff()
 return f
def adjoint(g,cs):return diffn(g,4)+diffn(cs[3]*g,3)-diffn(cs[2]*g,2)+(cs[1]*g).diff()-cs[0]*g

def run(a0,C0,z0):
 a=J.var(a0,1);C=J.var(C0,0);z=J.var(z0,2)
 d=source_data(a,C,z);d['C']=C
 cs=monic_coeffs(d)
 A=d['A'];B=A.diff();Dnum=d['Dnum']
 g2=A**4*Dnum/(24*B**4)
 s1=(Dnum-adjoint(g2,cs))/A
 residue=d['Hz']*s1.diff(1)-d['Ha']*s1.diff(2)
 baseline=Dnum/A
 baseline_residue=d['Hz']*baseline.diff(1)-d['Ha']*baseline.diff(2)
 return {'prime':PRIME,'jet_orders':{'C':CMAX,'parameter_total':PMAX},'point':{'a':a0,'C':C0,'z':z0},'R0':d['R'].const(),'R0_a':d['R'].diff(1).const(),'R0_z':d['R'].diff(2).const(),'H':d['H'].const(),'Ha':d['Ha'].const(),'Hz':d['Hz'].const(),'N':(3*d['H']-2*C*d['h']).const(),'Delta':(4*C**6-729*d['H']**4).const(),'Y_R0':A.const(),'delta_Y_R0':B.const(),'Dnum':Dnum.const(),'g2':g2.const(),'s1':s1.const(),'simple_residue_Y_s1':residue.const(),'baseline_s1':baseline.const(),'baseline_Y_s1':baseline_residue.const()}
if __name__=='__main__':
 import sys
 point=tuple(map(int,sys.argv[1:4]))
 out=run(*point)
 dest=Path(os.environ.get('R0_RESULT_PATH','/workspace/off-paired-research-new/coupled-fresh/rank4-relative/two-operator/R0-simple-residue-results.json'))
 dest.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
