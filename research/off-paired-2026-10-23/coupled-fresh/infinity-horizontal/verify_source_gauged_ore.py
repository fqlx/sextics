"""Exact source-preserving infinity gauge killing the normal-log coefficient."""
import sympy as s,json
from pathlib import Path
from math import comb
C,H=s.symbols('C H',nonzero=True);D=4*C**6-729*H**4
root=Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative')
ore=json.loads((root/'infinity-ore-general.json').read_text())
U=[s.sympify(x,locals={'C':C,'H':H})for x in ore['U']]
V=[s.sympify(x,locals={'C':C,'H':H})for x in ore['V']]
M=[s.sympify(x,locals={'C':C,'H':H})for x in ore['M']]
c=[-55*C**2/D,-309*C**3/D,-(271*C**6-1458*H**4)/(C**2*D),-2*(32*C**6+729*H**4)/(C*D)]
L=[-x for x in c]+[s.Integer(1)]
R=[(24200*C**12-596322*C**6*H**4-7971615*H**8)/(C**3*D**2),2*(3452*C**12-226719*C**6*H**4+3188646*H**8)/(C**2*D**2),3*(100*C**6+2187*H**4)/(2*C*D),s.Integer(1)]
S=[2494800*C**2*H**2/D**2,3954825*C**3*H**2/D**2,2835*H**2*(595*C**6-1458*H**4)/(C**2*D**2),5670*H**2*(44*C**6+729*H**4)/(C*D**2),2835*H**2/D]
def trim(a):
 while a and a[-1]==0:a.pop()
 return a
def add(a,b,k=1):return trim([s.cancel((a[i]if i<len(a)else 0)+k*(b[i]if i<len(b)else 0))for i in range(max(len(a),len(b)))])
def mul(a,b):
 out=[s.Integer(0)]*(len(a)+len(b)-1)
 for i,aa in enumerate(a):
  for j,bb in enumerate(b):
   for k in range(i+1):out[i+j-k]+=aa*comb(i,k)*s.diff(bb,C,k)
 return trim([s.cancel(x)for x in out])
def adj(a):
 out=[s.Integer(0)]*len(a)
 for i,aa in enumerate(a):
  for j in range(i+1):out[j]+=(-1)**i*comb(i,j)*s.diff(aa,C,i-j)
 return trim([s.cancel(x)for x in out])
checks=[]
checks.append(not add(mul(R,L),mul(S,M),-1))
r=11*D**2*C/(1786050*H**4)
Ug=add(U,[s.cancel(r*x)for x in R],-1)
Vg=add(V,[s.cancel(r*x)for x in S])
checks.append(not add(add(mul(Ug,L),mul(Vg,M)),[s.Integer(1)],-1))
Bg=adj(Vg)
checks.append(s.cancel(sum(x*s.diff(C**2,C,j)for j,x in enumerate(Bg)))==0)
# Right divide Bg by theta−2; no residue means no logarithmic coefficient.
def rightdiv(a,b):
 rem=a[:];q=[s.Integer(0)]*max(0,len(a)-len(b)+1)
 while len(rem)>=len(b):
  n=len(rem)-len(b);v=s.cancel(rem[-1]/b[-1]);q[n]=v;rem=add(rem,mul([0]*n+[v],b),-1)
 return trim(q),rem
Bt,rem=rightdiv(Bg,[-2,C]);checks.append(not rem)
assert all(checks),checks
out={'checks':len(checks),'passed':True,'meaning':'Ug L+Vg M=1, Bg=Vg*=Bt(theta−2), hence Bg(C²)=0; no horizontal curl solved','R':[str(s.factor(x))for x in R],'S':[str(s.factor(x))for x in S],'r':str(s.factor(r)),'Ug':[str(s.factor(x))for x in Ug],'Vg':[str(s.factor(x))for x in Vg],'Bg':[str(s.factor(x))for x in Bg],'Bt':[str(s.factor(x))for x in Bt]}
Path(__file__).with_name('source-gauged-ore.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
