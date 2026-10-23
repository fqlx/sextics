"""Canonical closed-time module with arbitrary rational kappa coefficients.

Work over the full-G36 generic kappa fiber, a cubic t algebra. Generators are
closed base df,dlog f. A relation with coefficients f_j(kappa) gives a closed
actual beta because dF is proportional to d(kappa). No degree bounds in
kappa are imposed. This does not cover arbitrary relative one-forms.
"""
import json,sys
from pathlib import Path
import sympy as S
import numpy as np
from closed_form_closure import z,U,K,t,qs,phys,hs,encode
root=Path(__file__).parent
sys.path.insert(0,str(root.parents[1]/'additive'))
from block_modular import solve_mod

H,B,C=phys
def pb(F,G):return 3*z**2*(S.diff(F,z)*S.diff(G,U)-S.diff(F,U)*S.diff(G,z))+6*t*(S.diff(F,K)*S.diff(G,t)-S.diff(F,t)*S.diff(G,K))
def Z(f):return 3*C*H/B*pb(B,f)-H*pb(C,f)-2*C*pb(H,f)

def generators():
 exact=['z','U','K','t','D','a=1+zK','b=2+3zU','H0=1+z2','C0=z^-2+U6','C1=K6/t','B1=zUK/2']
 logs=['z','U','K','t','H','C','a=1+zK','b=2+3zU','H0=1+z2','C0=z^-2+U6','B0=U/2+K/3']
 labels=[];enc=[]
 for mode,names in [('d',exact),('dlog',logs)]:
  for name in names:
   h=hs[name];value=Z(h)/(h if mode=='dlog'else 1)
   labels.append(mode+'('+name+')');enc.append(encode(value,qs))
 return labels,enc

def algebra(vals,kappa,p):
 zz,uu,kk=map(int,vals);h0=(1+zz*zz)%p;c0=(pow(zz,-2,p)+pow(uu,6,p))%p;c1=pow(kk,6,p)
 bv=(uu*pow(2,-1,p)+kk*pow(3,-1,p)+zz*uu*kk*pow(2,-1,p))%p
 lead=kappa*c0%p
 if not lead:raise ZeroDivisionError
 il=pow(lead,-1,p)
 f=[kappa*c1*h0*h0%p*il%p,
    (kappa*(c0*h0*h0+2*c1*h0)-pow(bv,3,p))%p*il%p,
    kappa*(2*c0*h0+c1)%p*il%p]
 def mul(a,b):
  out=[0]*5
  for i in range(3):
   for j in range(3):out[i+j]=(out[i+j]+int(a[i])*int(b[j]))%p
  for i in [4,3]:
   for j in range(3):out[i-3+j]=(out[i-3+j]-out[i]*f[j])%p
  return out[:3]
 def inverse(a):
  mat=[[0]*4 for _ in range(3)]
  for j in range(3):
   e=[0]*3;e[j]=1;column=mul(a,e)
   for i in range(3):mat[i][j]=column[i]
  mat[0][3]=1
  for j in range(3):
   row=next((i for i in range(j,3)if mat[i][j]),None)
   if row is None:raise ZeroDivisionError
   mat[j],mat[row]=mat[row],mat[j];iv=pow(mat[j][j],-1,p)
   mat[j]=[v*iv%p for v in mat[j]]
   for i in range(3):
    if i==j:continue
    q=mat[i][j];mat[i]=[(a-q*b)%p for a,b in zip(mat[i],mat[j])]
  return[mat[i][3]for i in range(3)]
 powers=[[1,0,0]]
 def poly(terms):
  out=[0]*3
  for ex,num,den in terms:
   while len(powers)<=ex[3]:powers.append(mul(powers[-1],[0,1,0]))
   coef=num*pow(den,-1,p)%p
   for v,e in zip([zz,uu,kk],ex[:3]):coef=coef*pow(v,e,p)%p
   out=[(a+coef*b)%p for a,b in zip(out,powers[ex[3]])]
  return out
 def evaluate(encoded):return mul(poly(encoded[0]),inverse(poly(encoded[1])))
 return evaluate

def witness_rows(matrix,p):
 A=matrix.copy();nr,nc=A.shape;ids=list(range(nr));row=0;used=[]
 for col in range(nc):
  picks=np.flatnonzero(A[row:,col])
  if not len(picks):continue
  pick=row+int(picks[0]);A[[row,pick]]=A[[pick,row]];ids[row],ids[pick]=ids[pick],ids[row]
  used.append(ids[row]);iv=pow(int(A[row,col]),-1,p);A[row]=(A[row]*iv)%p
  for i in range(row+1,nr):A[i]=(A[i]-A[i,col]*A[row])%p
  row+=1
  if row==nc:break
 return used

def run(p=1009,kappa=1):
 labels,enc=generators();rng=np.random.default_rng(172954);points=[];blocks=[]
 while len(points)<40:
  pt=rng.integers(1,p,size=3,dtype=np.int64)
  try:ev=algebra(pt,kappa,p);block=np.array([ev(e)for e in enc],dtype=np.int64).T
  except ZeroDivisionError:continue
  points.append([int(x)for x in pt]);blocks.append(block)
 matrix=np.vstack(blocks);rhs=np.tile(np.array([1,0,0],dtype=np.int64),len(points))
 rank,sol=solve_mod(matrix,rhs,p)
 report={'prime':p,'kappa_evaluation':kappa,'generators':labels,'unknown_coefficient_field':'k(kappa), k characteristic zero',
  'sampled_base_points':points,'rank':rank,'rows':len(rhs),'consistent':sol is not None,
  'generic_fiber_equation':'kappa*(c0*t+c1)*(t+h0)^2-B^3*t=0',
  'module_scope':'arbitrary rational kappa coefficients on the 22 canonical relative-closed time forms'}
 if sol is None:
  augmented=np.column_stack((matrix,rhs));ids=witness_rows(augmented,p)
  report['augmented_rank']=len(ids)
  if len(ids)==len(labels)+1:
   report['nonzero_augmented_minor_rows']=ids
   report['nonzero_augmented_minor_mod_p']=augmented[ids].tolist()
   report['status']='nonzero augmented minor rejects this canonical k(kappa) module; no general primitive exclusion'
  else:report['status']='sample inconsistent but generic-module rank needs further analysis; no candidate'
 else:
  report['evaluated_candidate']={name:int(c)for name,c in zip(labels,sol)if c}
  report['status']='candidate only at evaluated kappa; requires fresh fibers and rational-function reconstruction'
 (root/'relative-time-module-results.json').write_text(json.dumps(report,indent=2))
 print(json.dumps({k:v for k,v in report.items()if k not in ['sampled_base_points','nonzero_augmented_minor_mod_p']},indent=2))
if __name__=='__main__':run()
