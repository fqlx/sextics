"""Rational rank-seven source-carrying current with two physical finite poles.

Poles s1=-3X0*Y1/2 and s2=-X0^3*Y0/X1^2. Tests D=X0^k.
Connection entries are exact rational functions evaluated modulo a prime;
no polynomial coefficient conclusion follows from a sampled consistency.
"""
import sympy as s,numpy as np,json,argparse,time
from pathlib import Path
from functools import lru_cache
root=Path(__file__).parent
raw=json.loads((root/'reconstructed-connection.json').read_text());moving=json.loads((root/'moving-pole-connection.json').read_text())
H,C,r=s.symbols('H C r');third=json.loads((root/'third-kind-connection.json').read_text());bs=[0,1,3,4,-1,-1,2];weights=[2,1,3]

def poly_evaluate(terms,vals,p):
 result=np.zeros(len(vals[0]),dtype=np.int64);powers={}
 for e,coefficient in terms:
  a=np.full(len(result),coefficient,dtype=np.int64)
  for i,k in enumerate(e):
   if (i,k)not in powers:powers[i,k]=np.array([pow(int(v),k,p)for v in vals[i]],dtype=np.int64)
   a=a*powers[i,k]%p
  result=(result+a)%p
 return result
@lru_cache(None)
def rat_terms(expr,p):
 num,den=s.fraction(s.factor(expr));out=[]
 for q in [num,den]:
  out.append([(e,int(c.p)*pow(int(c.q),-1,p)%p)for e,c in s.Poly(q,H,C,r).terms()])
 return out

def rat_evaluate(expr,vals,p):
 num,den=rat_terms(expr,p);nn=poly_evaluate(num,vals,p);dd=poly_evaluate(den,vals,p)
 assert np.all(dd),str(expr)
 return nn*np.array([pow(int(a),-1,p)for a in dd],dtype=np.int64)%p

def connection(points,p):
 x,y,z=points.T;inv2=pow(2,-1,p);inv3=pow(3,-1,p)
 xp={k:np.array([pow(int(a),k,p)for a in x],dtype=np.int64)for k in range(7)}
 yp={k:np.array([pow(int(a),k,p)for a in y],dtype=np.int64)for k in range(7)}
 zp={k:np.array([pow(int(a),k,p)for a in z],dtype=np.int64)for k in range(7)}
 xi=np.array([pow(int(a),-1,p)for a in x],dtype=np.int64)
 hv=(1+xp[6]+yp[6]+zp[6]+x*y%p*z*inv2)%p;cv=(xp[3]*z*inv2+x*y*inv3)%p
 dh=[(6*xp[5]+y*z*inv2)%p,(6*yp[5]+x*z*inv2)%p,(6*zp[5]+x*y*inv2)%p]
 dc=[(3*xp[2]*z*inv2+y*inv3)%p,x*inv3%p,xp[3]*inv2%p]
 zero=np.zeros(len(x),dtype=np.int64)
 poles=[-3*z*inv2%p,-y*xi%p*xi%p]
 dpoles=[[zero,zero,np.full(len(x),-3*inv2%p,dtype=np.int64)],[(2*y*xi%p*xi%p*xi)%p,-xi*xi%p,zero]]
 mh=np.zeros((7,7,len(x)),dtype=np.int64);mc=mh.copy();mr=[mh.copy(),mh.copy()]
 for j in range(4):
  for k in range(4):
   mh[k,j]=rat_evaluate(s.sympify(raw['H']['columns'][j][k]),[hv,cv,poles[0]],p)
   mc[k,j]=rat_evaluate(s.sympify(raw['C']['columns'][j][k]),[hv,cv,poles[0]],p)
 for k in range(4):
  mh[k,6]=rat_evaluate(s.sympify(third['columns']['H'][k]),[hv,cv,poles[0]],p)
  mc[k,6]=rat_evaluate(s.sympify(third['columns']['C'][k]),[hv,cv,poles[0]],p)
 for q in range(2):
  col=4+q
  for i,k in enumerate([0,1,2,3,col]):
   mh[k,col]=rat_evaluate(s.sympify(moving['columns']['H'][i]),[hv,cv,poles[q]],p)
   mc[k,col]=rat_evaluate(s.sympify(moving['columns']['C'][i]),[hv,cv,poles[q]],p)
   mr[q][k,col]=rat_evaluate(s.sympify(moving['columns']['r'][i]),[hv,cv,poles[q]],p)
 bi=[(mh*dh[i]+mc*dc[i]+mr[0]*dpoles[0][i]+mr[1]*dpoles[1][i])%p for i in range(3)]
 source=(-mh[:,0]*yp[3]*pow(6,-1,p))%p
 return bi,source

def monomials(degree,char):
 if degree<0:return[]
 return[(a,b,c)for a in range(degree+1)for b in range(degree-a+1)for c in range(degree-a-b+1)if(2*a+b+3*c)%6==char]
def solve_mod(mat,rhs,p):
 a=np.column_stack((mat,rhs)).copy();m,n=mat.shape;row=0;pivots=[]
 for col in range(n):
  ids=np.flatnonzero(a[row:,col])
  if not len(ids):continue
  k=row+int(ids[0]);a[[row,k]]=a[[k,row]];a[row]=a[row]*pow(int(a[row,col]),-1,p)%p
  ids=np.flatnonzero(a[row+1:,col])+row+1
  for off in range(0,len(ids),128):
   q=ids[off:off+128];a[q]=(a[q]-a[q,col,None]*a[row])%p
  pivots.append(col);row+=1
  if row==m:break
 if np.any(np.all(a[:,:n]==0,axis=1)&(a[:,n]!=0)):return len(pivots),None
 sol=np.zeros(n,dtype=np.int64)
 for k,c in reversed(list(enumerate(pivots))):sol[c]=(a[k,n]-int(a[k,c+1:n]@sol[c+1:])%p)%p
 return len(pivots),sol

def sample_points(count,p,seed):
 rng=np.random.default_rng(seed);points=[]
 while len(points)<count:
  x,y,z=map(int,rng.integers(1,p,size=3));h=(1+pow(x,6,p)+pow(y,6,p)+pow(z,6,p)+x*y*z*pow(2,-1,p))%p;c=(pow(x,3,p)*z*pow(2,-1,p)+x*y*pow(3,-1,p))%p
  rr=[-3*z*pow(2,-1,p)%p,-y*pow(x,-2,p)%p]
  if not h or not(4*pow(c,6,p)-729*pow(h,4,p))%p:continue
  if any(not((h+c*a)**2-4*pow(a,6,p))%p for a in rr):continue
  points.append((x,y,z))
 return np.array(points,dtype=np.int64)
def matrix_for(labels,points,p):
 bi,source=connection(points,p);mat=np.zeros((len(points)*7,len(labels)),dtype=np.int64)
 for col,(i,j,e)in enumerate(labels):
  mm=poly_evaluate([(e,1)],points.T,p)
  for k in range(7):mat[k::7,col]=mm*bi[i][k,j]%p
  if e[i]:
   ee=tuple(a-(1 if q==i else 0)for q,a in enumerate(e));mat[j::7,col]=(mat[j::7,col]+poly_evaluate([(ee,e[i])],points.T,p))%p
 return mat,source.T.reshape(-1)
def run(k,p):
 labels=[(i,j,e)for i in range(3)for j,index in enumerate(bs)for e in monomials(k+1-2*index,(3+weights[i]-3*index)%6)]
 points=sample_points(len(labels)+12,p,27841+k);mat,rhs=matrix_for(labels,points,p)
 start=time.monotonic();rank,sol=solve_mod(mat,rhs,p)
 out={'denominator':f'X0^{k}','prime':p,'unknowns':len(labels),'rows':len(rhs),'rank':rank,'consistent_evaluations':sol is not None,'solve_seconds':time.monotonic()-start}
 if sol is not None:
  fresh=sample_points(400,p,856341+k);fm,frhs=matrix_for(labels,fresh,p);res=(fm@sol-frhs)%p;out['fresh_nonzero_residuals']=int(np.count_nonzero(res))
  out['candidate']=[{'i':i,'basis_index':j,'monomial':e,'coefficient':int(a)}for(i,j,e),a in zip(labels,sol)if a]
 print(json.dumps({k:v for k,v in out.items()if k!='candidate'}),flush=True);return out
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--k',type=int,nargs='+',default=list(range(6)));parser.add_argument('--prime',type=int,default=1009);args=parser.parse_args();out=[]
 for k in args.k:
  out.append(run(k,args.prime));(root/'two-pole-infinity-current-search-results.json').write_text(json.dumps(out,indent=2))
