"""Complete normalized fixed-support certificate test for cyclic-triple-residual.
Only exact mu3(X2) and global-Y characters are used.  All Q terms retained.
"""
from pathlib import Path
from hashlib import sha256
import json, pickle, time, sys
import sympy as s, yaml
from flint import nmod_mat
HERE=Path(__file__).resolve().parent
REC=Path('/workspace/sextics/data/cyclic-triple-residual/instance.rec')
z=s.symbols('X0 X1 X2 Y0 Y1 Y2'); prime=1000003
rec=yaml.safe_load(REC.read_text()); F=s.Poly(rec['F'],*z); A=s.Poly(rec['A'],*z)
D=s.Poly(z[2]**6+z[3]**6+z[4]**6+z[5]**6,*z)
Fint=s.Poly(7*F.as_expr(),*z); grad=[Fint.diff(t) for t in z]; dg=[D.diff(t) for t in z]
def mons(d,n=6):
 if n==1:
  yield (d,);return
 for j in range(d+1):
  for t in mons(d-j,n-1):yield (j,)+t

def char(m):return (m[2]%3,sum(m[3:])%2)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
num=[(i,m) for i in range(6) for m in mons(7) if char(m)==((1 if i==2 else 0),(1 if i<3 else 0))]
quo=[m for m in mons(6) if char(m)==(0,1)]
rows=[m for m in mons(12) if char(m)==(0,1)]; ri={m:i for i,m in enumerate(rows)}
cols=num+[(6,m) for m in quo]; ci={x:i for i,x in enumerate(cols)}
n=len(rows); nc=len(cols)
sparse=[]
for i,m in num:
 c={}
 for e,a in grad[i].terms():c[ri[add(m,e)]]=int(a)
 if m[i]:
  mm=list(m);mm[i]-=1
  for e,a in D.terms():
   r=n+ri[add(mm,e)];c[r]=c.get(r,0)+7*int(a)*m[i]
 for e,a in dg[i].terms():
  if not a:continue
  r=n+ri[add(m,e)];c[r]=c.get(r,0)-7*int(a)
 sparse.append({r:a for r,a in c.items() if a})
for m in quo:sparse.append({n+ri[add(m,e)]:-int(a) for e,a in Fint.terms()})
rhs={ri[e]:int(a) for e,a in s.Poly(7*A.as_expr()*D.as_expr(),*z).terms()}
print('dimensions',2*n,nc,'Ni',len(num),'Q',len(quo),flush=True)
# Homogeneous normalized solutions from arbitrary linear vector fields V of the
# prescribed source character: N=F V - (V(F)/6) Z, Q=D div V - V(D).
# Exact integer coefficient vectors use 42*N and 42*Q.
kernels=[]; labels=[]
for i in range(6):
 for j in range(6):
  if char(tuple(int(k==j) for k in range(6))) != ((1 if i==2 else 0),(1 if i<3 else 0)):continue
  vf=F.diff(z[i]).as_expr()*z[j]
  Nv=[s.Poly(42*((F.as_expr()*z[j] if k==i else 0)-vf*z[k]/6),*z) for k in range(6)]
  Qv=s.Poly(42*((D.as_expr() if i==j else 0)-dg[i].as_expr()*z[j]),*z)
  v=[0]*nc
  for k,P in enumerate(Nv):
   for e,a in P.terms():
    if a:v[ci[k,e]]=int(a)
  for e,a in Qv.terms():
   if a:v[ci[6,e]]=int(a)
  out={}
  for a,c in zip(v,sparse):
   if not a:continue
   for r,b in c.items():out[r]=out.get(r,0)+a*b
  assert not any(out.values()),('kernel identity failed',i,j)
  kernels.append(v);labels.append([i,j])
kr=nmod_mat(kernels,prime).rank()
print('exact homogeneous kernels',len(kernels),'independent mod p',kr,flush=True)
assert kr==len(kernels)
start=time.monotonic(); dense=[[0]*nc for _ in range(2*n)]
for j,c in enumerate(sparse):
 for r,a in c.items():dense[r][j]=a%prime
M=nmod_mat(dense,prime);rank=M.rank(); print('coefficient rank',rank,flush=True)
aug=nmod_mat([rr+[rhs.get(i,0)%prime] for i,rr in enumerate(dense)],prime)
ra=aug.rank();print('augmented rank',ra,flush=True)
upper=nc-len(kernels)
result=dict(instance=rec['id'],instanceRecSHA256=sha256(REC.read_bytes()).hexdigest(),F=str(F.as_expr()),A=str(A.as_expr()),D=str(D.as_expr()),q=rec['q'],prime=prime,rows=2*n,numeratorColumns=len(num),quotientColumns=len(quo),columns=nc,coefficientRankMod=rank,augmentedRankMod=ra,exactKernelDimensionLowerBound=len(kernels),coefficientRankQUpperBound=upper,kernelLabels=labels,allKernelIdentitiesExact=True,kernelIndependenceRankMod=kr,seconds=round(time.monotonic()-start,3))
if ra>rank and rank==upper:result['status']='exact characteristic-zero exclusion by rank sandwich'
elif ra>rank:result['status']='finite-prime inconsistency only; characteristic-zero rank upper bound not sharp'
else:result['status']='modular candidate; rational reconstruction required'
(HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
with (HERE/'packet.pickle').open('wb') as f:pickle.dump(dict(F=F,A=A,D=D,z=z,num=num,quo=quo,rows=rows,columns=sparse,rhs=rhs,kernels=kernels,prime=prime),f)
print(json.dumps(result,indent=2),flush=True)
