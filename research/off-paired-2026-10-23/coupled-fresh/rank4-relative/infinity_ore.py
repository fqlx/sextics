"""Exact Ore left Bezout for compact PF and infinity derivative operator."""
import sympy as s,json
from pathlib import Path
C=s.symbols('C');Dlt=4*C**6-729
clean=lambda v:s.cancel(v)
def trim(A):
 while A and A[-1]==0:A.pop()
 return A
def add(A,B):return trim([clean((A[i]if i<len(A)else 0)+(B[i]if i<len(B)else 0))for i in range(max(len(A),len(B)))])
def scale(A,c):return trim([clean(c*x)for x in A])
def mul(A,B):
 R=[s.Integer(0)]*max(0,len(A)+len(B)-1)
 for i,a in enumerate(A):
  for j,b in enumerate(B):
   for k in range(i+1):R[i-k+j]+=s.binomial(i,k)*a*s.diff(b,C,k)
 return trim([clean(x)for x in R])
def divleft(A,B):
 R=A[:];Q=[]
 while len(R)>=len(B):
  n=len(R)-len(B);q=[s.Integer(0)]*n+[clean(R[-1]/B[-1])]
  Q=add(Q,q);R=add(R,scale(mul(q,B),-1))
 return Q,R
cs=[-55*C*C/Dlt,-309*C**3/Dlt,-(271*C**6-1458)/(C*C*Dlt),-2*(32*C**6+729)/(C*Dlt)]
L=[-cs[0],-cs[1],-cs[2],-cs[3],s.Integer(1)]
M=[2*C**3/567,46*C**4/2835,(20*C**6+2187)/(1890*C),Dlt/2835]
A,B=L,M;UA,VA=[s.Integer(1)],[];UB,VB=[],[s.Integer(1)]
while B:
 Q,R=divleft(A,B)
 print('Ore orders',len(A)-1,len(B)-1,'remainder',len(R)-1,flush=True)
 UR=add(UA,scale(mul(Q,UB),-1));VR=add(VA,scale(mul(Q,VB),-1))
 A,B=B,R;UA,UB=UB,UR;VA,VB=VB,VR
assert len(A)==1
UA=scale(UA,1/A[0]);VA=scale(VA,1/A[0])
assert add(mul(UA,L),mul(VA,M))==[1]
print('Verified exact left Bezout; orders',len(UA)-1,len(VA)-1,flush=True)
out={'scope':'H=1 normalized C family','meaning':'U L+V M=1; formal adjoint gives L* U*+M* V*=1',
'U_coefficients_low_to_high':[str(s.factor(x))for x in UA], 'V_coefficients_low_to_high':[str(s.factor(x))for x in VA],
'L_coefficients_low_to_high':[str(x)for x in L], 'M_coefficients_low_to_high':[str(x)for x in M]}
Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/infinity-ore-bezout.json').write_text(json.dumps(out,indent=2)+'\n')
