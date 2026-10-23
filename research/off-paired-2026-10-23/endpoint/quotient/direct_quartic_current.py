"""Direct strict polynomial current on exact weighted G=v^2F, actual source t^3v^4/3.

Variables order t,u,v,z,a,b; t currentzero. This is a certificate attempt,
not an endpoint cohomology ansatz. Any hit requires exact identity andPiola lift.
"""
import sympy as s,json,time
from pathlib import Path
root=Path(__file__).parent
t,u,v,z,a,b=s.symbols('t u v z a b');vs=[u,v,z,a,b];weights=[2,3,1,1,1];signs=[1,1,1,0,1];chars=[0,0,0,1,5]
G=u**6+v**4+(t**6+z**6+a**6+b**6+t**3*u*z/2+t**2*u*a*b/3)*v**2+u**3*z*a*b*v/2
source=t**3*v**4/3

def mons(n,i):
 def rec(j,remaining,e):
  if j==5:
   if sum(x*y for x,y in zip(e,chars))%6==chars[i] and sum(x*y for x,y in zip(e,signs))%2==signs[i]:yield tuple(e)
   return
  for k in range(remaining//weights[j]+1):yield from rec(j+1,remaining-k*weights[j],e+[k])
 return list(rec(0,n,[]))

def run():
 labels=[];cols=[]
 for i,w in enumerate(weights):
  for e in mons(3+w,i):
   n=t**(3+w-sum(x*y for x,y in zip(e,weights)))*s.prod(x**k for x,k in zip(vs,e))
   col=s.Poly(s.expand(-n*s.diff(G,vs[i])+G*s.diff(n,vs[i])),t,*vs)
   labels.append((i,e));cols.append(col.as_dict())
 rhs=s.Poly(-source,t,*vs).as_dict();rows=sorted(set(rhs).union(*(col.keys()for col in cols)))
 mat=s.MutableSparseMatrix(len(rows),len(cols),{});ri={e:i for i,e in enumerate(rows)}
 for j,col in enumerate(cols):
  for e,c in col.items():mat[ri[e],j]=c
 rr=s.Matrix([rhs.get(e,0)for e in rows]);p=1009
 sparsecols=[{ri[e]:int(c.p)*pow(int(c.q),-1,p)%p for e,c in col.items()}for col in cols]
 rhsmod={ri[e]:int(c.p)*pow(int(c.q),-1,p)%p for e,c in rhs.items()}
 def rank(cs):
  piv={}
  for cc in cs:
   q={e:c%p for e,c in cc.items()if c%p}
   while q:
    k=min(q)
    if k not in piv:
     inv=pow(q[k],-1,p);piv[k]={e:c*inv%p for e,c in q.items()};break
    scale=q[k]
    for e,c in piv[k].items():
     val=(q.get(e,0)-scale*c)%p
     if val:q[e]=val
     elif e in q:del q[e]
  return len(piv)
 rank0=rank(sparsecols);rank1=rank(sparsecols+[rhsmod]);out={'unknowns':len(labels),'rows':len(rows),'prime':p,'rank':rank0,'augmented_rank':rank1,'actual_source':'t^3*v^4/3','target':'G=v^2F','strict_polynomial_current':rank0==rank1}
 if rank0==rank1:
  sol=s.linsolve((mat,rr));vec=list(sol)[0];params=set().union(*(x.free_symbols for x in vec));vec=[x.subs({p:0 for p in params})for x in vec]
  NN=[0]*5
  for q,(i,e)in zip(vec,labels):NN[i]+=q*t**(3+weights[i]-sum(x*y for x,y in zip(e,weights)))*s.prod(x**k for x,k in zip(vs,e))
  assert s.expand(source+sum(-NN[i]*s.diff(G,vs[i])+G*s.diff(NN[i],vs[i])for i in range(5)))==0
  out['exact_numerators']=[str(s.factor(n))for n in NN]
 (root/'direct-quartic-current-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':run()
