"""Exact right Bezout for the coupled PE/PD residue and P3 residue images.

Only a residue-module identity is claimed. All other Hermite terms remain
obligations until the full rational potentials/current are substituted.
"""
import json
from pathlib import Path
import sympy as s
u=s.symbols('u');clean=s.cancel
def trim(a):
 while a and a[-1]==0:a.pop()
 return a
def add(a,b):return trim([clean((a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0))for i in range(max(len(a),len(b)))])
def scale(a,c):return trim([clean(c*x)for x in a])
def mul(a,b):
 if not a or not b:return []
 out=[s.Integer(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):
   for k in range(i+1):out[i-k+j]+=s.binomial(i,k)*x*s.diff(y,u,k)
 return trim([clean(x)for x in out])
def adj(a):
 out=[]
 for j,c in enumerate(a):out=add(out,mul([0]*j+[(-1)**j],[c]))
 return out
def divleft(a,b):
 out=[];rem=a[:]
 while len(rem)>=len(b):
  q=[0]*(len(rem)-len(b))+[clean(rem[-1]/b[-1])]
  out=add(out,q);rem=add(rem,scale(mul(q,b),-1))
 return out,rem
theta=[0,u];one=[1]
Q=[0,3*(2-u),u*(4-u)]
L1=scale(mul(add(theta,one),Q),2)
L2=scale(mul(mul(theta,add(one,scale(theta,-2))),add(one,scale(theta,-1))),-4)
A,B=adj(L1),adj(L2)
UA,VA=[1],[];UB,VB=[],[1];steps=[]
while B:
 q,rem=divleft(A,B);steps.append((len(A)-1,len(B)-1,len(rem)-1))
 ur=add(UA,scale(mul(q,UB),-1));vr=add(VA,scale(mul(q,VB),-1))
 A,B=B,rem;UA,UB=UB,ur;VA,VB=VB,vr
if len(A)==1:
 UA=scale(UA,1/A[0]);VA=scale(VA,1/A[0])
 assert add(mul(UA,adj(L1)),mul(VA,adj(L2)))==[1]
 U,V=adj(UA),adj(VA)
 assert add(mul(L1,U),mul(L2,V))==[1]
else:U=V=[]
out={'steps':steps,'left_gcd_order':len(A)-1,
 'L1':'2(theta+1)[u(4-u)partial_u^2+3(2-u)partial_u]',
 'L2':'-4 theta(1-2theta)(1-theta)',
 'meaning':'L1 U+L2 V=1 EXACTLY if left_gcd_order=0; source residue t=U r,T=V r',
 'U_low_to_high':[str(s.factor(x))for x in U],
 'V_low_to_high':[str(s.factor(x))for x in V],
 'certificate':False,
 'scope':'residue images only; all rational lifting, other poles and full (Z-1) source retained as obligations'}
Path(__file__).with_name('residue-ore-bezout-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
