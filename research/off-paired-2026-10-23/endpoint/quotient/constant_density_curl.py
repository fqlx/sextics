"""Sourceconstant quotient currents with rational residue-closed finite-pole potentials."""
import constant_density_current as q
import numpy as np,json,time,argparse
from pathlib import Path
root=Path(__file__).parent;rows=[0,1,2,3,6]
def eps(i,l,j):
 if len({i,l,j})!=3:return 0
 return 1 if(i,l,j)in[(0,1,2),(1,2,0),(2,0,1)]else -1

def labels_for(k,m):
 labels=[];d=3*m+k
 for i in range(3):
  for j,index in enumerate([0,1,3,4,2]):
   for e in q.monomials(d+q.weights[i]-3-2*index,(m+index+1)%2):labels.append(('current',i,rows[j],e))
 for pole in range(2):
  for coord in range(3):
   for e in q.monomials(d+5-q.weights[coord],(m+1)%2):labels.append(('potential',pole,coord,e))
 return labels

def matrix_for(labels,points,p,m):
 bi,source=q.connection(points,p);mat=np.zeros((len(points)*5,len(labels)),dtype=np.int64)
 vi=np.array([pow(int(v),-1,p)for v in points[:,1]],dtype=np.int64);dd=np.array([pow(int(v),m,p)for v in points[:,1]],dtype=np.int64)
 for col,(kind,i,j,e)in enumerate(labels):
  mm=q.old.poly_evaluate([(e,1)],points.T,p)
  if kind=='current':
   for k,row in enumerate(rows):mat[k::5,col]=mm*bi[i][row,j]%p
   if e[i]:
    ee=tuple(a-(1 if h==i else 0)for h,a in enumerate(e));position=rows.index(j)
    mat[position::5,col]=(mat[position::5,col]+q.old.poly_evaluate([(ee,e[i])],points.T,p))%p
   if i==1:mat[rows.index(j)::5,col]=(mat[rows.index(j)::5,col]-m*mm*vi)%p
  else:
   polecol=4+i;vv=np.zeros((3,len(points)),dtype=np.int64)
   for coord in range(3):
    for l in range(3):
     sign=eps(coord,l,j)
     if not sign:continue
     derivative=np.zeros(len(points),dtype=np.int64)
     if e[l]:
      ee=tuple(a-(1 if h==l else 0)for h,a in enumerate(e));derivative=q.old.poly_evaluate([(ee,e[l])],points.T,p)
     vv[coord]=(vv[coord]+sign*(derivative+mm*bi[l][polecol,polecol]-(m*mm*vi if l==1 else 0)))%p
   for k,row in enumerate(rows):mat[k::5,col]=sum(vv[coord]*bi[coord][row,polecol]for coord in range(3))%p
 return mat,(source[rows]*dd).T.reshape(-1)
def run(k,m,p):
 labels=labels_for(k,m);points=q.sample_points(len(labels)+12,p,95917+k+29*m);mat,rhs=matrix_for(labels,points,p,m)
 start=time.monotonic();rank,sol=q.old.solve_mod(mat,rhs,p)
 out={'denominator':f'X0^{k}*v^{m}','prime':p,'unknowns':len(labels),'rows':len(rhs),'rank':rank,'consistent_evaluations':sol is not None,'solve_seconds':time.monotonic()-start}
 if sol is not None:
  fresh=q.sample_points(400,p,45791+k+7*m);fm,fr=matrix_for(labels,fresh,p,m);out['fresh_nonzero_residuals']=int(np.count_nonzero((fm@sol-fr)%p))
  out['candidate']=[{'type':kind,'i':i,'j':j,'monomial':e,'coefficient':int(a)}for(kind,i,j,e),a in zip(labels,sol)if a]
 print(json.dumps({a:b for a,b in out.items()if a!='candidate'}),flush=True);return out
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--cases',nargs='+',default=['0,0','1,0','2,0','3,0','0,1','1,1','2,1','3,1']);parser.add_argument('--prime',type=int,default=1009);args=parser.parse_args();out=[]
 for case in args.cases:
  k,m=map(int,case.split(','));out.append(run(k,m,args.prime));(root/'constant-density-curl-results.json').write_text(json.dumps(out,indent=2))
