"""Normalized exact Ore syzygy, retaining infinity matching freedom."""
import sympy as s,json
from pathlib import Path
from math import comb
C=s.symbols('C');H=s.Integer(1)
root=Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative')
d=json.loads((root/'cyclic_pf.json').read_text())
cs=[s.sympify(x,locals={'b':C})for x in d['coefficients']]
L=[-x for x in cs]+[s.Integer(1)]
ore=json.loads((root/'infinity-ore-general.json').read_text())
M=[s.sympify(x,locals={'C':C,'H':H})for x in ore['M']]
def trim(x):
 while x and x[-1]==0:x.pop()
 return x
def add(a,b,k=1):return trim([s.cancel((a[i]if i<len(a)else 0)+k*(b[i]if i<len(b)else 0))for i in range(max(len(a),len(b)))])
def mul(a,b):
 out=[s.Integer(0)]*(len(a)+len(b)-1)
 for i,aa in enumerate(a):
  for j,bb in enumerate(b):
   for k in range(i+1):out[i+j-k]+=aa*comb(i,k)*s.diff(bb,C,k)
 return trim([s.cancel(x)for x in out])
def div(a,b):
 rem=a[:];q=[s.Integer(0)]*max(0,len(a)-len(b)+1)
 while len(rem)>=len(b):
  n=len(rem)-len(b);v=s.cancel(rem[-1]/b[-1]);q[n]=v
  rem=add(rem,mul([s.Integer(0)]*n+[v],b),-1)
 return trim(q),rem
qr=[]
for j in range(4):
 qr.append(div(mul([s.Integer(0)]*j+[s.Integer(1)],L),M))
 print('division',j,flush=True)
A=s.Matrix([[qr[j][1][i]if i<len(qr[j][1])else 0 for j in range(3)]for i in range(3)])
rhs=s.Matrix([-(qr[3][1][i]if i<len(qr[3][1])else 0)for i in range(3)])
sol=[s.factor(x)for x in A.inv()*rhs]
R=sol+[s.Integer(1)]
S=[s.Integer(0)]
for r,(q,rem)in zip(R,qr):S=add(S,[s.cancel(r*x)for x in q])
S=[s.factor(x)for x in S]
assert not add(mul(R,L),mul(S,M),-1)
out={'meaning':'R L=S M normalized H=1; formal adjoint L*R*=M*S* gives source-preserving shifts f+=R*eta,xi+=S*eta','R_low_to_high':[str(x)for x in R],'S_low_to_high':[str(x)for x in S]}
Path(__file__).with_name('infinity-syzygy-normalized.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
