"""Native rational solve of all8 boundary derivatives simultaneously."""
from pathlib import Path
import pickle,json,time
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
HERE=Path(__file__).parent;start=time.monotonic();packet=pickle.loads((HERE/'boundary_linear_packet.pickle').read_bytes())
ctx=fmpq_mpoly_ctx.get(packet['variables'])
class RF:
 def __init__(self,n=0,d=1):
  if isinstance(n,RF):self.n,self.d=n.n,n.d;return
  if not isinstance(n,fmpq_mpoly):n=ctx.constant(fmpq(n))
  if not isinstance(d,fmpq_mpoly):d=ctx.constant(fmpq(d))
  if not n:self.n,self.d=n,ctx.constant(1);return
  assert d
  g=n.gcd(d);n=n//g;d=d//g;lc=d.leading_coefficient();self.n,self.d=n/lc,d/lc
 def __neg__(a):return RF(-a.n,a.d)
 def __add__(a,b):
  b=RF(b);g=a.d.gcd(b.d);ad=a.d//g;bd=b.d//g
  return RF(a.n*bd+b.n*ad,a.d*bd)
 __radd__=__add__
 def __sub__(a,b):return a+-RF(b)
 def __rsub__(a,b):return RF(b)+-a
 def __mul__(a,b):
  b=RF(b);g=a.n.gcd(b.d);h=b.n.gcd(a.d)
  return RF((a.n//g)*(b.n//h),(a.d//h)*(b.d//g))
 __rmul__=__mul__
 def __truediv__(a,b):b=RF(b);return a*RF(b.d,b.n)
 def payload(a):return{'numerator':{tuple(map(int,e)):str(c)for e,c in a.n.to_dict().items()},'denominator':{tuple(map(int,e)):str(c)for e,c in a.d.to_dict().items()}}
 def cost(a):return len(a.n.to_dict())+len(a.d.to_dict())
zero=RF(0)
def load(v):return RF(ctx.from_dict({e:fmpq(c)for e,c in v['num'].items()}),ctx.from_dict({e:fmpq(c)for e,c in v['den'].items()}))
A=[[load(v)for v in row]for row in packet['A']]
labels=[(name,j)for name in ['L','r','x','s']for j in range(2)]
rhs=[[load(packet['RHS'][name][j][i])for name,j in labels]for i in range(len(A))]
rows,cols=packet['row_pivots'],packet['column_pivots'];n=len(rows);m=len(labels)
M=[[A[i][j]for j in cols]+rhs[i][:]for i in rows];perm=list(cols)
for k in range(n):
 cost,i,j=min((M[i][j].cost(),i,j)for i in range(k,n)for j in range(k,n)if M[i][j].n)
 if i!=k:M[k],M[i]=M[i],M[k]
 if j!=k:
  for rr in M:rr[k],rr[j]=rr[j],rr[k]
  perm[k],perm[j]=perm[j],perm[k]
 pivot=M[k][k]
 for j in range(k+1,n+m):M[k][j]=M[k][j]/pivot
 M[k][k]=RF(1)
 for i in range(k+1,n):
  q=M[i][k]
  if not q.n:continue
  M[i][k]=zero
  for j in range(k+1,n+m):M[i][j]=M[i][j]-q*M[k][j]
 print('PIVOT',k,cost,round(time.monotonic()-start,3),flush=True)
ans=[[zero for j in range(m)]for i in range(n)]
for i in range(n-1,-1,-1):
 for j in range(m):ans[i][j]=M[i][n+j]-sum((M[i][k]*ans[k][j]for k in range(i+1,n)),zero)
full=[[zero for j in range(m)]for i in range(len(A[0]))]
for i,col in enumerate(perm):full[col]=ans[i]
for i in range(len(A)):
 for j in range(m):assert not(sum((A[i][k]*full[k][j]for k in range(len(full))),zero)-rhs[i][j]).n
print('EXACT_ALL19',round(time.monotonic()-start,3),flush=True)
conn={};prims={}
for jj,(name,boundary)in enumerate(labels):
 conn.setdefault(name,[]).append([full[i][jj].payload()for i in range(5)])
 prims.setdefault(name,[]).append([full[i][jj].payload()for i in range(5,len(full))])
result={'variables':packet['variables'],'connection_boundary':conn,'primitive_coefficients':prims,'primitive_labels':packet['Q_labels'],'basis':'properglobaleta_clean3+sigma0,sigma1','primitive_convention':'residue of i_Q Omega/(D*C), hence affine +(QW-WQh)/(D*Ct)','all19_coefficients_verified':True,'seconds':time.monotonic()-start}
(HERE/'boundary_native.pickle').write_bytes(pickle.dumps(result))
(HERE/'boundary_native.json').write_text(json.dumps({'all19_coefficients_verified':True,'seconds':time.monotonic()-start,'connection_terms':{name:[[len(e['numerator'])for e in row]for row in mat]for name,mat in conn.items()}},indent=2)+'\n')
print('DONE',round(time.monotonic()-start,3),flush=True)
