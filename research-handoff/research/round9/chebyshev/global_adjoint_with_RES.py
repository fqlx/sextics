# INVALID geometric filtration; retained only as arithmetic replay of discarded upperjetshortage. See trace_duals.py and actual_dual_weights.json.
from pathlib import Path
import sympy as S,json,math
P=Path(__file__).parent;budgets=[(12,1),(4,2),(8,5),(12,6),(8,3),(16,3)];q=S.symbols('q');J=S.Poly(q**6+1,q)
constraints=[[]for _ in budgets]
def add(i,qside,hv,js,ks=(0,)):
 for j in js:
  for k in ks:constraints[i].append((qside,hv,j,k))
add(0,'inf',0,range(2))
for i in(0,3,5):
 for j in range(6):constraints[i].append(('J','inf',j,0))
for hv in(-2,2):
 for i in(1,4,5):add(i,'zero',hv,[0])
 for i in(2,3):
  add(i,'zero',hv,range(3));add(i,'zero',hv,[0],[1]);add(i,'inf',hv,[0])
add(2,'zero',0,range(3));add(2,'inf',0,range(7))
add(3,'inf',0,range(8));add(3,'inf',0,range(2),[1])
add(4,'inf',0,range(4));add(5,'inf',0,range(6))
res=[]
for i,(n,m)in enumerate(budgets):
 cols=[(a,b)for a in range(n+1)for b in range(m+1)];rows=[]
 for side,hv,j,k in constraints[i]:
  row=[]
  for a,b in cols:
   if side=='J':v=(S.Poly(q**a,q).rem(J).nth(j)if b==m else 0)
   else:
    qa=(int(a==j)if side=='zero'else int(a==n-j));hh=(math.comb(b,k)*hv**(b-k)if b>=k else 0);v=qa*hh
   row.append(v)
  rows.append(row)
 M=S.Matrix(rows);rank=M.rank();res.append({'dual_index':i,'budget':[n,m],'conditions':len(rows),'rank':rank,'section_dimension':len(cols),'jet_descriptions':constraints[i]});print({k:v for k,v in res[-1].items()if k!='jet_descriptions'},flush=True)
(P/'global_adjoint_with_RES.json').write_text(json.dumps({'checks':res,'total_conditions':sum(x['conditions']for x in res),'scope':'EXACT simultaneous interpolation onto the proposed boundary canonical-jet upper spaces. Does not prove those spaces capture all geometric adjoint defects; normalized strict-transform/resolution audit remains essential.'},indent=2)+'\n')
