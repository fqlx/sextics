"""Independent exact full5 GM curvature and residue-block audit over QQ(L,r,x,s)."""
from pathlib import Path
import pickle,json,time
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
HERE=Path(__file__).parent;start=time.monotonic();names=('L','r','x','s');ctx=fmpq_mpoly_ctx.get(names)
class F:
 def __init__(self,n=0,d=1):
  if isinstance(n,F):self.n,self.d=n.n,n.d;return
  self.n=n if isinstance(n,fmpq_mpoly)else ctx.constant(n);self.d=d if isinstance(d,fmpq_mpoly)else ctx.constant(d)
  assert self.d
  if not self.n:self.d=ctx.constant(1);return
  g=self.n.gcd(self.d);self.n//=g;self.d//=g
  lc=self.d.leading_coefficient();self.n/=lc;self.d/=lc
 def __add__(a,b):
  b=F(b);g=a.d.gcd(b.d)
  return F(a.n*(b.d//g)+b.n*(a.d//g),a.d*(b.d//g))
 __radd__=__add__
 def __neg__(a):return F(-a.n,a.d)
 def __sub__(a,b):return a+-F(b)
 def __mul__(a,b):
  b=F(b);g=a.n.gcd(b.d);h=b.n.gcd(a.d)
  return F((a.n//g)*(b.n//h),(a.d//h)*(b.d//g))
 __rmul__=__mul__
 def derivative(a,i):return F(a.n.derivative(i)*a.d-a.n*a.d.derivative(i),a.d*a.d)
 def __bool__(a):return bool(a.n)
def load(q):
 if isinstance(q['numerator'],dict):
  conv=lambda dd:ctx.from_dict({tuple(e):fmpq(c)for e,c in dd.items()})
  return F(conv(q['numerator']),conv(q['denominator']))
 return F(fmpq_mpoly(q['numerator'],ctx),fmpq_mpoly(q['denominator'],ctx))
proper=pickle.load(open(HERE.parent/'cyclic_full'/'global_eta_complete.pickle','rb'));bp=pickle.load(open(HERE.parent/'open_curve'/'boundary_native.pickle','rb'))
conn={}
for name in names:
 M=[[F(0)for _ in range(5)]for _ in range(5)]
 if name!='s':
  for i in range(3):
   for j in range(3):M[i][j]=load(proper['connection'][name][i][j])
 for i in range(2):
  for j in range(5):M[i+3][j]=load(bp['connection_boundary'][name][i][j])
 conn[name]=M
# Independently closed residue formula, no packet matrix imported.
AA=F(fmpq_mpoly('5/7*(1+s)',ctx));BB=F(fmpq_mpoly('L+r*s',ctx))+F(fmpq_mpoly('s^3',ctx),fmpq_mpoly('x',ctx))
DD=AA*AA-F(4)*BB
# F division is intentionally implemented by reversing numerator/denominator.
def div(a,b):return a*F(b.d,b.n)
for k,name in enumerate(names):
 da,db=AA.derivative(k),BB.derivative(k)
 RR=[[div(-AA*BB*da+(F(10)*BB-F(2)*AA*AA)*db,F(3)*BB*DD),div(F(4)*BB*da-F(2)*AA*db,F(3)*BB*DD)],
     [div(F(2)*BB*da-AA*db,F(3)*DD),div(-F(2)*AA*da+F(4)*db,F(3)*DD)]]
 assert all(not(conn[name][i+3][j+3]-RR[i][j])for i in range(2)for j in range(2))
checks={}
for i in range(4):
 for j in range(i+1,4):
  Ni,Nj=conn[names[i]],conn[names[j]];nonzero=[]
  for a in range(5):
   for b in range(5):
    val=Nj[a][b].derivative(i)-Ni[a][b].derivative(j)+sum((Nj[a][k]*Ni[k][b]-Ni[a][k]*Nj[k][b]for k in range(5)),F(0))
    if val:nonzero.append((a,b))
  assert not nonzero,(i,j,nonzero)
  checks[names[i]+names[j]]=True
  print('EXACT_CURVATURE',names[i],names[j],time.monotonic()-start,flush=True)
  (HERE/'rank5_flatness_partial.json').write_text(json.dumps({'checked':checks,'seconds':time.monotonic()-start},indent=2)+'\n')
result={'variables':names,'all6_full5_curvatures_exact_zero':True,'all16_residue_block_entries_match_closed_formula':True,'curvature_convention':'partial_i N_j-partial_j N_i+N_j*N_i-N_i*N_j=0; basis derivatives are rows.','checks':checks,'method':'Independent rational arithmetic over native FLINT polynomials; parsed off boundary packet and literal complete proper frame, without importing assemble/native_rf/residue packet.','scope':'Exact compatibility audit of the full rank5 connection. No source PDE solution is claimed.','seconds':time.monotonic()-start}
(HERE/'rank5_flatness_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
