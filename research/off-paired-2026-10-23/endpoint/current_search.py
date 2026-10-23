"""Source-carrying rank-four current search over F_p; candidates need exact lift.

Square-root convention Z=b^6−a^6 binds the source sign below.
Connection columns mean ∇v omega_j=sum_k Mv[k,j] omega_k.
Solve Σ_i(∂i a_i+(MH H_i+MC C_i)a_i)=−A MH e0/6.
Homogeneous degree of a_i,j is 1−2j. X0 component is zero.
"""
import sympy as s
import numpy as np
import json, argparse, time
from functools import lru_cache
from pathlib import Path
root=Path(__file__).parent
raw=json.loads((root/'reconstructed-connection.json').read_text())
H,C=s.symbols('H C'); t,x,y,z=s.symbols('t x y z'); vs=[x,y,z]; bs=[0,1,3,4]
L=4*H*(4*C**6-729*H**4)
M={v:s.Matrix.hstack(*(s.Matrix([s.sympify(a)for a in col])for col in raw[v]['columns']))for v in ['H','C']}
AH=(L*M['H']).applyfunc(s.cancel); AC=(L*M['C']).applyfunc(s.cancel)
HH=t**6+x**6+y**6+z**6+t**3*x*y*z/2; CC=x**3*z/2+t**2*x*y/3; AA=t**3*y**3
sub={H:HH,C:CC}; Li=L.subs(sub)
B=[(AH*HH.diff(v)+AC*CC.diff(v)).subs(sub)for v in vs]

def monomials(n,char):
 if n<0:return []
 return [(a,b,c)for a in range(n+1)for b in range(n-a+1)for c in range(n-a-b+1)if (2*a+b+3*c)%6==char]
@lru_cache(None)
def poly(expr,p):
 return [(e,int(c.p)*pow(int(c.q),-1,p)%p)for e,c in s.Poly(s.sympify(expr).subs(t,1),x,y,z).terms()]
def evaluate(terms,points,p):
 val=np.zeros(len(points),dtype=np.int64)
 powers={}
 for e,c in terms:
  w=np.full(len(points),c,dtype=np.int64)
  for i in range(3):
   key=(i,e[i])
   if key not in powers:powers[key]=np.array([pow(int(a),e[i],p)for a in points[:,i]],dtype=np.int64)
   w=w*powers[key]%p
  val=(val+w)%p
 return val

def solve_mod(mat,rhs,p):
 a=np.column_stack((mat,rhs)).copy(); m,n=mat.shape; pivot=[]; row=0
 for col in range(n):
  ids=np.flatnonzero(a[row:,col])
  if not len(ids):continue
  r=row+int(ids[0]); a[[row,r]]=a[[r,row]]
  a[row]=a[row]*pow(int(a[row,col]),-1,p)%p
  ids=np.flatnonzero(a[row+1:,col])+row+1
  # bounded chunks save transient allocation.
  for off in range(0,len(ids),128):
   q=ids[off:off+128]; a[q]=(a[q]-a[q,col,None]*a[row])%p
  pivot.append(col);row+=1
  if row==m:break
 bad=np.flatnonzero((np.all(a[:,:n]==0,axis=1))&(a[:,n]!=0))
 if len(bad):return len(pivot),None
 sol=np.zeros(n,dtype=np.int64)
 for r,c in reversed(list(enumerate(pivot))):sol[c]=(a[r,n]-int(a[r,c+1:n]@sol[c+1:])%p)%p
 return len(pivot),sol

def run(name,D,p,seed):
 D=s.expand(D); d=s.Poly(D,t,x,y,z).total_degree()
 terms=s.Poly(D,t,x,y,z).terms();assert {sum(e)for e,c in terms}=={d}
 chars={(2*e[1]+e[2]+3*e[3])%6 for e,c in terms}; deltas=sorted(chars)
 labels=[(i,j,e)for i in range(3)for j,k in enumerate(bs)for delta in deltas for e in monomials(d+1-2*k,(3+delta+[2,1,3][i]-3*k)%6)]
 count=len(labels)+12
 rng=np.random.default_rng(seed);points=rng.integers(1,p,size=(count,3))
 dd=evaluate(poly(D,p),points,p);ll=evaluate(poly(Li,p),points,p)
 di=[evaluate(poly(D.diff(v),p),points,p)for v in vs]
 bb=[[[evaluate(poly(B[i][k,j],p),points,p)for j in range(4)]for k in range(4)]for i in range(3)]
 aa=evaluate(poly(AA,p),points,p); rr=np.column_stack([-aa*dd%p*dd%p*evaluate(poly(AH[k,0].subs(sub),p),points,p)*pow(6,-1,p)%p for k in range(4)]).reshape(-1)
 mat=np.zeros((count*4,len(labels)),dtype=np.int64)
 for col,(i,j,e) in enumerate(labels):
  mm=evaluate([(e,1)],points,p)
  for k in range(4):mat[k::4,col]=mm*dd%p*bb[i][k][j]%p
  derivative=evaluate([(tuple(a-(1 if h==i else 0)for h,a in enumerate(e)),e[i])],points,p)if e[i] else np.zeros(count,dtype=np.int64)
  mat[j::4,col]=(mat[j::4,col]+ll*(dd*derivative%p-mm*di[i]%p))%p
 start=time.monotonic();rank,sol=solve_mod(mat,rr,p)
 out={'name':name,'denominator':str(D),'degree':d,'prime':p,'seed':seed,'unknowns':len(labels),'rows':len(rr),'rank':rank,'consistent_evaluations':sol is not None,'seconds':time.monotonic()-start}
 print(json.dumps(out),flush=True)
 if sol is not None:
  out['candidate']=[{'i':i,'j':bs[j],'monomial':e,'coefficient':int(a)}for (i,j,e),a in zip(labels,sol)if a]
 return out

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--cases',nargs='+',default=['minus','plus','W0','W1','W2','J01','J02','J12']);parser.add_argument('--prime',type=int,default=1009);parser.add_argument('--output',default='current-search-results.json');args=parser.parse_args()
 W=[2*CC*HH.diff(v)-3*HH*CC.diff(v)for v in vs]
 J={(i,j):HH.diff(vs[i])*CC.diff(vs[j])-HH.diff(vs[j])*CC.diff(vs[i])for i in range(3)for j in range(i+1,3)}
 cases={'one':s.Integer(1),'H':HH,'C':CC,'C2':CC**2,'HC':HH*CC,'H2':HH**2,'minus':2*CC**3-27*HH**2,'plus':2*CC**3+27*HH**2,'delta':4*CC**6-729*HH**4}
 cases.update({f'W{i}':w for i,w in enumerate(W)});cases.update({f'R{r}W{i}':3*HH*CC.diff(v)+r*CC*HH.diff(v)for r in [1,4]for i,v in enumerate(vs)});cases.update({'xC2':x*CC**2,'x2C2':x**2*CC**2,'x3C2':x**3*CC**2,'xJ01':x*J[(0,1)],'x3J01':x**3*J[(0,1)],'J01sq':J[(0,1)]**2});cases.update({f'J{i}{j}':v for (i,j),v in J.items()})
 output=[]
 for name in args.cases:
  output.append(run(name,cases[name],args.prime,72063+len(output)))
  (root/args.output).write_text(json.dumps(output,indent=2))
