"""Constructive modular screen: compact Fs^-1 currents plus closed pole currents.

The source is the immutable physical x,y,z target. No unrestricted exclusion
follows from a failed screen. Any hit requires exact lifting and source checks.
"""
import sys,json,time
from pathlib import Path
import numpy as np
sys.path.insert(0,'/workspace/off-paired-research-new/endpoint')
import weighted_curl_current_search as w
q=w.q
p=1009
rows=w.rows
compact=[a for a in w.labels_for(12)if a[0]=='current']
potentials=[a for a in w.labels_for(0)if a[0]=='potential']
labels=compact+potentials

def denominator(points):
 x,y,z=points.T
 inv2=pow(2,-1,p);inv3=pow(3,-1,p)
 pw=lambda a,k:np.array([pow(int(v),k,p)for v in a],dtype=np.int64)
 H=(1+pw(x,6)+pw(y,6)+pw(z,6)+x*y%p*z*inv2)%p
 C=(pw(x,3)*z*inv2+x*y*inv3)%p
 r=-3*z*inv2%p
 D=((H+C*r%p)**2-4*pw(r,6))%p
 assert np.all(D)
 return np.array([pow(int(d),-1,p)for d in D],dtype=np.int64)

def matrix(points):
 bi,src=q.connection(points,p)
 n=len(points);mat=np.zeros((n*5,len(labels)),dtype=np.int64)
 invD=denominator(points)
 for col,label in enumerate(compact):
  kind,i,j,e=label
  mm=q.poly_evaluate([(e,1)],points.T,p)
  val=mm*invD%p
  for k,row in enumerate(rows):mat[k::5,col]=val*bi[i][row,j]%p
  derivative=np.zeros(n,dtype=np.int64)
  if e[i]:
   ee=tuple(a-(1 if h==i else 0)for h,a in enumerate(e))
   derivative=q.poly_evaluate([(ee,e[i])],points.T,p)*invD%p
  # D_i/D = -2 times the first beta's diagonal connection.
  derivative=(derivative+2*val*bi[i][4,4])%p
  pos=rows.index(j)
  mat[pos::5,col]=(mat[pos::5,col]+derivative)%p
 if potentials:
  pm,_=w.matrix_for(potentials,points,p)
  mat[:,len(compact):]=pm
 return mat,src[rows].T.reshape(-1)

start=time.monotonic()
points=q.sample_points(len(labels)+12,p,794573)
mat,rhs=matrix(points)
print('Built',mat.shape,'in',time.monotonic()-start,'seconds',flush=True)
rank,sol=q.solve_mod(mat,rhs,p)
out={'prime':p,'denominator':'F_s for compact currents; F_s and F_t from weighted curls','compact_unknowns':len(compact),'potential_unknowns':len(potentials),'rows':len(rhs),'rank':rank,'consistent_evaluations':sol is not None,'seconds':time.monotonic()-start,'status':'restricted constructive screen only'}
if sol is not None:
 fresh=q.sample_points(400,p,847231)
 fm,fr=matrix(fresh)
 out['fresh_nonzero_residuals']=int(np.count_nonzero((fm@sol-fr)%p))
 out['candidate']=[{'label':lab,'coefficient':int(a)}for lab,a in zip(labels,sol)if a]
Path(__file__).with_name('fs-compact-current-search-results.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:v for k,v in out.items()if k!='candidate'}),flush=True)
