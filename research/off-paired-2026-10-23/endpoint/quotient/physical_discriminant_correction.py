"""Actual constant-source correction with compact and normal-function common pole.

For s1=-3z/2 or s2=-v/u^2, compact currents are P/F_s, F_s=f(s).
Residue-closed beta_s currents are sqrt(F_s)curl(A/sqrt(F_s)); A remains
polynomial on the affine chart. This differs from prior polynomial compact
currents plus finite-pole potentials. Any hit needs exact reconstruction.
"""
import constant_density_current as q
from constant_density_curl import eps
import numpy as np,json,argparse,time
from pathlib import Path
root=Path(__file__).parent;rows=[0,1,2,3,6]

def labels_for(k):
 labels=[]
 for i in range(3):
  for j,index in enumerate([0,1,3,4,2]):
   for e in q.monomials(12+k+q.weights[i]-3-2*index,(index+1)%2):labels.append(('current',i,rows[j],e))
 for coord in range(3):
  for e in q.monomials(k+5-q.weights[coord],1):labels.append(('potential',0,coord,e))
 return labels

def eval_fs(points,p,pole):
 u,v,z=points.T;ui=np.array([pow(int(a),-1,p)for a in u],dtype=np.int64);vi=np.array([pow(int(a),-1,p)for a in v],dtype=np.int64)
 power=lambda arr,n:np.array([pow(int(a),n,p)for a in arr],dtype=np.int64)
 h=(1+power(u,6)*vi%p*vi+v*v+power(z,6)+u*z*pow(2,-1,p))%p
 c=(power(u,3)*z%p*vi%p*pow(2,-1,p)+u*pow(3,-1,p))%p
 r=-3*z*pow(2,-1,p)%p if pole==1 else -v*ui%p*ui%p
 S=(h+c*r)%p
 return (S*S-4*power(r,6))%p

def matrix_for(labels,points,p,pole):
 bi,source=q.connection(points,p);mat=np.zeros((len(points)*5,len(labels)),dtype=np.int64);fs=eval_fs(points,p,pole);colbeta=3+pole
 for col,(kind,i,j,e)in enumerate(labels):
  mm=q.old.poly_evaluate([(e,1)],points.T,p)
  if kind=='current':
   for k,row in enumerate(rows):mat[k::5,col]=mm*bi[i][row,j]%p
   derivative=np.zeros(len(points),dtype=np.int64)
   if e[i]:
    ee=tuple(a-(1 if h==i else 0)for h,a in enumerate(e));derivative=q.old.poly_evaluate([(ee,e[i])],points.T,p)
   position=rows.index(j)
   mat[position::5,col]=(mat[position::5,col]+derivative+2*mm*bi[i][colbeta,colbeta])%p
  else:
   vv=np.zeros((3,len(points)),dtype=np.int64)
   for coord in range(3):
    for l in range(3):
     sign=eps(coord,l,j)
     if not sign:continue
     derivative=np.zeros(len(points),dtype=np.int64)
     if e[l]:
      ee=tuple(a-(1 if h==l else 0)for h,a in enumerate(e));derivative=q.old.poly_evaluate([(ee,e[l])],points.T,p)
     vv[coord]=(vv[coord]+sign*(derivative+mm*bi[l][colbeta,colbeta]))%p
   for k,row in enumerate(rows):mat[k::5,col]=sum(vv[coord]*bi[coord][row,colbeta]%p*fs for coord in range(3))%p
 return mat,(source[rows]*fs).T.reshape(-1)

def run(k,pole,p):
 labels=labels_for(k);points=q.sample_points(len(labels)+12,p,729474+k+47*pole);mat,rhs=matrix_for(labels,points,p,pole)
 start=time.monotonic();rank,sol=q.old.solve_mod(mat,rhs,p)
 out={'pole':pole,'compact_denominator':'F_s*X0^'+str(k),'potential_affine_degree_extra':k,'prime':p,'unknowns':len(labels),'rows':len(rhs),'rank':rank,'consistent_evaluations':sol is not None,'solve_seconds':time.monotonic()-start}
 if sol is not None:
  fresh=q.sample_points(400,p,284731+k+17*pole);fm,fr=matrix_for(labels,fresh,p,pole);out['fresh_nonzero_residuals']=int(np.count_nonzero((fm@sol-fr)%p))
  out['candidate']=[{'type':kind,'i':i,'j':j,'monomial':e,'coefficient':int(a)}for(kind,i,j,e),a in zip(labels,sol)if a]
 print(json.dumps({a:b for a,b in out.items()if a!='candidate'}),flush=True);return out
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--cases',nargs='+',default=['1,0','2,0','1,1']);parser.add_argument('--prime',type=int,default=1009);args=parser.parse_args();out=[]
 for case in args.cases:
  pole,k=map(int,case.split(','));out.append(run(k,pole,args.prime));(root/'physical-discriminant-correction-results.json').write_text(json.dumps(out,indent=2))
