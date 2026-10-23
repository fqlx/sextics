from pathlib import Path
import pickle,json,hashlib,time
import sympy as s
from flint import nmod_mat
p=Path('/workspace/research/round10/fermat_cone_fixed/packet.pickle')
D=pickle.loads(p.read_bytes()); z=D['z'];F=D['F'];A=D['A'];g=D['D'];pr=D['prime']
rows=D['rows'];ri={e:i for i,e in enumerate(rows)}; n=len(rows)
def mon(e):return s.prod(x**k for x,k in zip(z,e))
def ch(e):return e[2]%3,sum(e[3:])%2
def mons(d,nv=6):
 if nv==1:yield(d,);return
 for j in range(d+1):
  for t in mons(d-j,nv-1):yield(j,)+t
# Complete source-type projections under actual automorphisms, independently from all homogeneous monomials.
num=[(i,e) for i in range(6) for e in mons(7) if ch(e)==(int(i==2),int(i<3))]
quo=[e for e in mons(6) if ch(e)==(0,1)]
assert num==D['num'] and quo==D['quo']
rebuilt=[]
for i,e in num:
 m=mon(e)
 polys=[s.Poly(7*m*F.diff(z[i]).as_expr(),*z),s.Poly(7*(g.as_expr()*s.diff(m,z[i])-m*g.diff(z[i]).as_expr()),*z)]
 col={}
 for block,P in enumerate(polys):
  for ee,a in P.terms():
   if a: col[block*n+ri[ee]]=int(a)
 rebuilt.append(col)
for e in quo:
 rebuilt.append({n+ri[ee]:int(a) for ee,a in s.Poly(-7*F.as_expr()*mon(e),*z).terms() if a})
assert rebuilt==D['columns']
rhs={ri[e]:int(a) for e,a in s.Poly(7*A.as_expr()*g.as_expr(),*z).terms() if a}
assert rhs==D['rhs']
M=[[0]*len(rebuilt) for _ in range(2*n)]
for j,col in enumerate(rebuilt):
 for i,a in col.items():M[i][j]=a%pr
rank=nmod_mat(M,pr).rank();aug=nmod_mat([r+[rhs.get(i,0)%pr] for i,r in enumerate(M)],pr).rank()
# Independently verify every exact homogeneous-kernel coefficient identity on the rebuilt operator.
for v in D['kernels']:
 out={}
 for a,col in zip(v,rebuilt):
  if a:
   for i,b in col.items():out[i]=out.get(i,0)+a*b
 assert not any(out.values())
kr=nmod_mat(D['kernels'],pr).rank()
assert rank==len(rebuilt)-kr and aug==rank+1
R=dict(all_operator_columns_rebuilt_by_direct_product_rule=True,source_character_projection_complete=True,rows=2*n,columns=len(rebuilt),rank=rank,augmented_rank=aug,independent_exact_kernels=kr,status='exact characteristic-zero fixed-support exclusion',packet_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
Path(__file__).with_suffix('.json').write_text(json.dumps(R,indent=2)+'\n');print(json.dumps(R,indent=2))
