"""Source-carrying minor-log residue class plus compact (z J01)^-1 currents.

A hit is only a modular candidate and requires independent exact lifting.
A failure is restricted constructive feedback, not a nonexistence theorem.
"""
import sys,json,time
from pathlib import Path
import sympy as s,numpy as np
sys.path.insert(0,'/workspace/off-paired-research-new/endpoint')
import weighted_curl_current_search as w
q=w.q;rows=w.rows
x,y,z=s.symbols('x y z');coords=[x,y,z]
H=1+x**6+y**6+z**6+x*y*z/2
C=x**3*z/2+x*y/3
rr=-3*z/2;L=s.expand(H+rr*C)
J=s.expand(s.diff(H,x)*s.diff(C,y)-s.diff(H,y)*s.diff(C,x))
lam=s.Matrix([s.diff(L,x),s.diff(L,y),s.diff(L,z)-3*L/z])
V=lam.cross(s.Matrix([s.diff(J,a)/J for a in coords]))
d=s.factor(sum(V[i]*s.diff(C,a)for i,a in enumerate(coords))-2*C*V[2]/z)
p=1009

def terms(poly):
 return[(e,int(c.p)*pow(int(c.q),-1,p)%p)for e,c in s.Poly(s.expand(poly),x,y,z).terms()]
D=z*J
Dterms=terms(D);Diterms=[terms(s.diff(D,a))for a in coords]
num,den=s.fraction(s.cancel(d));nt,dt=terms(num),terms(den)
def pe(t,pts):return q.poly_evaluate(t,pts.T,p)
def chosen_points(count,seed):
 pts=q.sample_points(count*2,p,seed)
 good=(pe(Dterms,pts)!=0)&(pe(dt,pts)!=0)
 pts=pts[good][:count]
 assert len(pts)==count
 return pts
labels=[('current',i,rows[j],e)for i in range(3)for j,index in enumerate([0,1,3,4,2])for e in q.monomials(11-2*index,(q.weights[i]-3*index)%6)]

def matrix(points):
 bi,src=q.connection(points,p);n=len(points)
 dd=pe(Dterms,points);inv=np.array([pow(int(a),-1,p)for a in dd],dtype=np.int64)
 di=[pe(t,points)for t in Diterms]
 mat=np.zeros((n*5,len(labels)+1),dtype=np.int64)
 for col,(kind,i,j,e)in enumerate(labels):
  mon=q.poly_evaluate([(e,1)],points.T,p);val=mon*inv%p
  for k,row in enumerate(rows):mat[k::5,col]=val*bi[i][row,j]%p
  der=np.zeros(n,dtype=np.int64)
  if e[i]:
   ee=tuple(a-(1 if b==i else 0)for b,a in enumerate(e))
   der=q.poly_evaluate([(ee,e[i])],points.T,p)*inv%p
  der=(der-val*di[i]%p*inv)%p
  k=rows.index(j);mat[k::5,col]=(mat[k::5,col]+der)%p
 dg=pe(nt,points)*np.array([pow(int(a),-1,p)for a in pe(dt,points)],dtype=np.int64)%p
 y3=np.array([pow(int(a),3,p)for a in points[:,1]],dtype=np.int64)
 mh=src[rows]*np.array([-6*pow(int(a),-1,p)%p for a in y3],dtype=np.int64)
 mat[:,-1]=(mh*dg).T.reshape(-1)%p
 return mat,src[rows].T.reshape(-1)

start=time.monotonic();pts=chosen_points(len(labels)+20,867219)
mat,rhs=matrix(pts)
print('Built',mat.shape,flush=True)
compact_rank,_=q.solve_mod(mat[:,:-1],np.zeros(len(rhs),dtype=np.int64),p)
rank,sol=q.solve_mod(mat,rhs,p)
out={'prime':p,'compact_denominator':'X0*z*J01','compact_unknowns':len(labels),'nonexact_log_classes':['g=J01'],'rows':len(rhs),'rank':rank,'compact_rank':compact_rank,'log_rank_gain':rank-compact_rank,'consistent_evaluations':sol is not None,'seconds':time.monotonic()-start,'scope':'restricted constructive screen only'}
if sol is not None:
 fm,fr=matrix(chosen_points(400,943172));out['fresh_nonzero_residuals']=int(np.count_nonzero((fm@sol-fr)%p))
 out['candidate']=[{'label':lab,'coefficient':int(c)}for lab,c in zip(labels+[('log_source','J01')],sol)if c]
Path(__file__).with_name('log-minor-zJ-current-search-results.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:v for k,v in out.items()if k!='candidate'}),flush=True)
