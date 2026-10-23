"""Rational source-current search with automatic finite-pole residue cancellation.

For each finite pole beta_s, V=curl(A)-grad(F_s)cross(A)/(2F_s).
Then div(V)-V(F_s)/(2F_s)=0 identically. Polynomial vectorpotentials
A have homogeneousweight4, represented onX0=1 withdegree<=k+4.
Compact and infinity-third-kind currents are included simultaneously.
"""
import two_pole_infinity_current_search as q
import numpy as np,json,time,argparse
from pathlib import Path
root=Path(__file__).parent
rows=[0,1,2,3,6]
def eps(i,l,j):
 if len({i,l,j})!=3:return 0
 return 1 if(i,l,j)in[(0,1,2),(1,2,0),(2,0,1)]else -1

def labels_for(k):
 labels=[]
 for i in range(3):
  for j,index in enumerate([0,1,3,4,2]):
   for e in q.monomials(k+1-2*index,(3+q.weights[i]-3*index)%6):labels.append(('current',i,rows[j],e))
 for pole in range(2):
  for component in range(3):
   for e in q.monomials(k+4,-q.weights[component]%6):labels.append(('potential',pole,component,e))
 return labels

def matrix_for(labels,points,p):
 bi,source=q.connection(points,p);mat=np.zeros((len(points)*5,len(labels)),dtype=np.int64)
 for col,label in enumerate(labels):
  kind,i,j,e=label;mm=q.poly_evaluate([(e,1)],points.T,p)
  if kind=='current':
   for k,row in enumerate(rows):mat[k::5,col]=mm*bi[i][row,j]%p
   if e[i]:
    ee=tuple(a-(1 if h==i else 0)for h,a in enumerate(e));position=rows.index(j)
    mat[position::5,col]=(mat[position::5,col]+q.poly_evaluate([(ee,e[i])],points.T,p))%p
  else:
   polecol=4+i
   vv=np.zeros((3,len(points)),dtype=np.int64)
   for coord in range(3):
    for l in range(3):
     sign=eps(coord,l,j)
     if not sign:continue
     derivative=np.zeros(len(points),dtype=np.int64)
     if e[l]:
      ee=tuple(a-(1 if h==l else 0)for h,a in enumerate(e));derivative=q.poly_evaluate([(ee,e[l])],points.T,p)
     vv[coord]=(vv[coord]+sign*(derivative+mm*bi[l][polecol,polecol]))%p
   for k,row in enumerate(rows):
    mat[k::5,col]=sum(vv[coord]*bi[coord][row,polecol]for coord in range(3))%p
 return mat,source[rows].T.reshape(-1)
def run(k,p):
 labels=labels_for(k);points=q.sample_points(len(labels)+12,p,94873+k);mat,rhs=matrix_for(labels,points,p)
 start=time.monotonic();rank,sol=q.solve_mod(mat,rhs,p)
 out={'affine_degree_parameter':k,'potential_max_affine_degree':k+4,'prime':p,'unknowns':len(labels),'rows':len(rhs),'rank':rank,'consistent_evaluations':sol is not None,'solve_seconds':time.monotonic()-start}
 if sol is not None:
  fresh=q.sample_points(400,p,762341+k);fm,fr=matrix_for(labels,fresh,p);out['fresh_nonzero_residuals']=int(np.count_nonzero((fm@sol-fr)%p))
  out['candidate']=[{'type':kind,'i':i,'j':j,'monomial':e,'coefficient':int(a)}for(kind,i,j,e),a in zip(labels,sol)if a]
 print(json.dumps({k:v for k,v in out.items()if k!='candidate'}),flush=True);return out
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--k',type=int,nargs='+',default=list(range(6)));parser.add_argument('--prime',type=int,default=1009);args=parser.parse_args();out=[]
 for k in args.k:
  out.append(run(k,args.prime));(root/'weighted-curl-current-search-results.json').write_text(json.dumps(out,indent=2))
