"""Actual constant-density quotient current. No certificate claimed.

u=x*y,v=y^3,z=Y1; source=-MH e0/18 du dv dz.
H=1+u6/v2+v2+z6+uz/2,C=u3*z/(2v)+u/3.
All compact4, infinityomega2 and both physical finite poles retained.
D=X0^k*v^m; weighted numerator degree 3m+k+w_i-3-2j.
"""
import sys,json,numpy as np,time,argparse
from pathlib import Path
root=Path(__file__).parent;sys.path.insert(0,str(root.parent))
import two_pole_infinity_current_search as old
s=old.s;bs=[0,1,3,4,-1,-1,2];weights=[2,3,1]

def connection(points,p):
 u,v,z=points.T;inv2=pow(2,-1,p);inv3=pow(3,-1,p)
 up={k:np.array([pow(int(a),k,p)for a in u],dtype=np.int64)for k in range(7)}
 vp={k:np.array([pow(int(a),k,p)for a in v],dtype=np.int64)for k in range(3)}
 zp={k:np.array([pow(int(a),k,p)for a in z],dtype=np.int64)for k in range(7)}
 ui=np.array([pow(int(a),-1,p)for a in u],dtype=np.int64);vi=np.array([pow(int(a),-1,p)for a in v],dtype=np.int64)
 hv=(1+up[6]*vi%p*vi+vp[2]+zp[6]+u*z*inv2)%p;cv=(up[3]*z%p*vi%p*inv2+u*inv3)%p
 dh=[(6*up[5]*vi%p*vi+z*inv2)%p,(-2*up[6]*vi%p*vi%p*vi+2*v)%p,(6*zp[5]+u*inv2)%p]
 dc=[(3*up[2]*z%p*vi%p*inv2+inv3)%p,-up[3]*z%p*vi%p*vi%p*inv2%p,up[3]*vi%p*inv2%p]
 zero=np.zeros(len(u),dtype=np.int64)
 poles=[-3*z*inv2%p,-v*ui%p*ui%p]
 dpoles=[[zero,zero,np.full(len(u),-3*inv2%p,dtype=np.int64)],[(2*v*ui%p*ui%p*ui)%p,-ui*ui%p,zero]]
 mh=np.zeros((7,7,len(u)),dtype=np.int64);mc=mh.copy();mr=[mh.copy(),mh.copy()]
 for j in range(4):
  for a in range(4):
   mh[a,j]=old.rat_evaluate(s.sympify(old.raw['H']['columns'][j][a]),[hv,cv,poles[0]],p)
   mc[a,j]=old.rat_evaluate(s.sympify(old.raw['C']['columns'][j][a]),[hv,cv,poles[0]],p)
 for a in range(4):
  mh[a,6]=old.rat_evaluate(s.sympify(old.third['columns']['H'][a]),[hv,cv,poles[0]],p)
  mc[a,6]=old.rat_evaluate(s.sympify(old.third['columns']['C'][a]),[hv,cv,poles[0]],p)
 for q in range(2):
  col=4+q
  for i,a in enumerate([0,1,2,3,col]):
   mh[a,col]=old.rat_evaluate(s.sympify(old.moving['columns']['H'][i]),[hv,cv,poles[q]],p)
   mc[a,col]=old.rat_evaluate(s.sympify(old.moving['columns']['C'][i]),[hv,cv,poles[q]],p)
   mr[q][a,col]=old.rat_evaluate(s.sympify(old.moving['columns']['r'][i]),[hv,cv,poles[q]],p)
 bi=[(mh*dh[i]+mc*dc[i]+mr[0]*dpoles[0][i]+mr[1]*dpoles[1][i])%p for i in range(3)]
 source=-mh[:,0]*pow(18,-1,p)%p
 return bi,source

def sample_points(count,p,seed):
 rng=np.random.default_rng(seed);out=[]
 while len(out)<count:
  u,v,z=map(int,rng.integers(1,p,size=3));h=(1+pow(u,6,p)*pow(v,-2,p)+v*v+pow(z,6,p)+u*z*pow(2,-1,p))%p;c=(pow(u,3,p)*z*pow(v,-1,p)*pow(2,-1,p)+u*pow(3,-1,p))%p
  poles=[-3*z*pow(2,-1,p)%p,-v*pow(u,-2,p)%p]
  if not h or not(4*pow(c,6,p)-729*pow(h,4,p))%p:continue
  if any(not((h+c*a)**2-4*pow(a,6,p))%p for a in poles):continue
  out.append((u,v,z))
 return np.array(out,dtype=np.int64)

def monomials(weight,parity):
 if weight<0:return[]
 return[(a,b,c)for a in range(weight//2+1)for b in range((weight-2*a)//3+1)for c in range(weight-2*a-3*b+1)if(a+b+c)%2==parity]
def labels_for(k,m):
 return[(i,j,e)for i in range(3)for j,index in enumerate(bs)for e in monomials(3*m+k+weights[i]-3-2*index,(m+index+1)%2)]
def matrix_for(labels,points,p,m):
 bi,source=connection(points,p);mat=np.zeros((len(points)*7,len(labels)),dtype=np.int64)
 vi=np.array([pow(int(v),-1,p)for v in points[:,1]],dtype=np.int64);dv=np.array([pow(int(v),m,p)for v in points[:,1]],dtype=np.int64)
 for col,(i,j,e)in enumerate(labels):
  mm=old.poly_evaluate([(e,1)],points.T,p)
  for a in range(7):mat[a::7,col]=mm*bi[i][a,j]%p
  if e[i]:
   ee=tuple(a-(1 if q==i else 0)for q,a in enumerate(e));mat[j::7,col]=(mat[j::7,col]+old.poly_evaluate([(ee,e[i])],points.T,p))%p
  if i==1:mat[j::7,col]=(mat[j::7,col]-mm*m*vi)%p
 return mat,(source*dv).T.reshape(-1)
def run(k,m,p):
 labels=labels_for(k,m);points=sample_points(len(labels)+12,p,85726+k+19*m);mat,rhs=matrix_for(labels,points,p,m)
 start=time.monotonic();rank,sol=old.solve_mod(mat,rhs,p)
 out={'denominator':f'X0^{k}*v^{m}','weighted_degree':k+3*m,'prime':p,'unknowns':len(labels),'rows':len(rhs),'rank':rank,'consistent_evaluations':sol is not None,'solve_seconds':time.monotonic()-start}
 if sol is not None:
  fresh=sample_points(400,p,434451+k+7*m);fm,fr=matrix_for(labels,fresh,p,m);out['fresh_nonzero_residuals']=int(np.count_nonzero((fm@sol-fr)%p))
  out['candidate']=[{'i':i,'basis_index':j,'monomial':e,'coefficient':int(a)}for(i,j,e),a in zip(labels,sol)if a]
 print(json.dumps({a:b for a,b in out.items()if a!='candidate'}),flush=True);return out
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--cases',nargs='+',default=['0,1','1,1','2,1','3,1','0,2','1,2','2,2']);parser.add_argument('--prime',type=int,default=1009);args=parser.parse_args();out=[]
 for case in args.cases:
  k,m=map(int,case.split(','));out.append(run(k,m,args.prime));(root/'constant-density-current-results.json').write_text(json.dumps(out,indent=2))
