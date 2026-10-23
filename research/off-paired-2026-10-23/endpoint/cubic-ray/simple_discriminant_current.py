"""One finite-connection constructive ansatz with simple D poles.

No degree escalation. These are the parent-specified bihomogeneous numerator
bounds for the actual cubic-ray source, with all four physical directions.
A modular hit must survive full point counts, fresh points, and exact lifting.
"""
import argparse,json,sys,time
from pathlib import Path
import numpy as np
root=Path(__file__).parent
sys.path.insert(0,str(root.parent/'additive'))
from block_modular import solve_mod

def labels_for():
 labels=[]
 for i in range(4):
  for j in range(2):
   nx=(5 if j==0 else 3)if i<2 else(4 if j==0 else 2)
   ny=(2 if j==0 else 4)if i<2 else(3 if j==0 else 5)
   for a in range(nx+1):
    for b in range(nx+1-a):
     for c in range(ny+1):
      for d in range(ny+1-c):labels.append((i,j,(a,b,c,d)))
 return labels

def field_data(points,p):
 x,a,u,v=points.T;pw=lambda ar,n:np.array([pow(int(z),n,p)for z in ar],dtype=np.int64)
 inv=lambda ar:np.array([pow(int(z),-1,p)for z in ar],dtype=np.int64)
 i2=pow(2,-1,p);i3=pow(3,-1,p)
 H=(1+pw(x,6)+pw(a,6))%p;C=(1+pw(u,6)+pw(v,6))%p
 B=(x*u*i2+pw(x,3)*a%p*u%p*v*i2+x*a%p*v*i3)%p
 D=(4*pw(B,3)+27*C*H%p*H)%p
 if np.any(C==0)or np.any(D==0):return None
 dH=np.array([6*pw(x,5),6*pw(a,5),0*x,0*x])%p
 dC=np.array([0*x,0*x,6*pw(u,5),6*pw(v,5)])%p
 dB=np.array([(u*i2+3*pw(x,2)*a%p*u%p*v*i2+a*v*i3)%p,
              (pw(x,3)*u%p*v*i2+x*v*i3)%p,
              (x*i2+pw(x,3)*a%p*v*i2)%p,
              (pw(x,3)*a%p*u*i2+x*a*i3)%p])
 idD=inv(D);idC=inv(C);b2=B*B%p;b3=b2*B%p;h2=H*H%p
 MH=np.array([[9*C*H,4*b2],[-6*B*C,18*C*H]])%p*idD%p
 MB=np.array([[2*b2,-6*B*H],[9*C*H,4*b2]])%p*idD%p
 MC=np.array([[-(2*b3+9*C*h2)%p*idC%p,2*b2*H%p*idC%p],
              [-3*B*H,-2*(2*b3+9*C*h2)%p*idC%p]])%p*idD%p
 connections=[(MH*dH[i]+MB*dB[i]+MC*dC[i])%p for i in range(4)]
 dlogD=[(12*b2*dB[i]+27*h2*dC[i]+54*C*H%p*dH[i])%p*idD%p for i in range(4)]
 # The entire current equation is multiplied by D once.
 rhs=np.array([B*(27*C*h2-2*b3)%p,-27*b2*C%p*H%p])%p*idD%p
 return connections,dlogD,rhs

def sample_points(n,p,seed):
 rng=np.random.default_rng(seed);out=[]
 while len(out)<n:
  pt=rng.integers(1,p,size=(1,4),dtype=np.int64)
  if field_data(pt,p)is not None:out.append(pt[0])
 return np.array(out,dtype=np.int64)

def matrix_for(labels,points,p):
 connections,dlogD,rhs=field_data(points,p)
 mons={};n=len(points);mat=np.zeros((2*n,len(labels)),dtype=np.int64)
 def mon(e):
  if e not in mons:
   value=np.ones(n,dtype=np.int64)
   for i,k in enumerate(e):
    for _ in range(k):value=value*points[:,i]%p
   mons[e]=value
  return mons[e]
 for col,(i,j,e)in enumerate(labels):
  mm=mon(e)
  for k in range(2):mat[k::2,col]=connections[i][k,j]*mm%p
  dm=0
  if e[i]:
   ee=tuple(a-(h==i)for h,a in enumerate(e));dm=e[i]*mon(ee)%p
  mat[j::2,col]=(mat[j::2,col]+dm-dlogD[i]*mm)%p
 return mat,rhs.T.reshape(-1)

def run(p,count):
 labels=labels_for();n=len(labels);assert n==1104
 report={'prime':p,'unknowns':n,'source':'B*s/(B+3*C*s^2)^3',
  'denominator':'D=4B^3+27CH^2','basis':['s','s^2+2B/(3C)'],
  'bounds':{'X_directions':{'e1':[5,2],'e2':[3,4]},'Y_directions':{'e1':[4,3],'e2':[2,5]}},
  'stages':[]}
 counts=[count]if count>=n else[count,n+12]
 for stage,npnt in enumerate(counts):
  print({'stage':stage,'generic_points':npnt,'building':True},flush=True)
  points=sample_points(npnt,p,913872+stage);mat,rhs=matrix_for(labels,points,p)
  start=time.monotonic();rank,sol=solve_mod(mat,rhs,p,progress=True)
  rec={'points':npnt,'rows':len(rhs),'rank':rank,'consistent':sol is not None,'seconds':time.monotonic()-start}
  report['stages'].append(rec)
  if sol is None:
   report['status']='inconsistent sampled modular ansatz; no candidate';break
  if npnt<n:
   print('Partial consistency is not a candidate; increasing generic points.',flush=True);continue
  points=sample_points(600,p,183741);mat,rhs=matrix_for(labels,points,p);res=(mat@sol-rhs)%p
  rec['fresh_nonzero_residuals']=int(np.count_nonzero(res))
  if np.any(res):report['status']='fresh-point residual rejected interpolation';break
  report['status']='modular candidate; requires rational reconstruction and full polynomial verification'
  report['candidate']=[{'direction':i,'basis_index':j,'monomial':e,'coefficient':int(a)}for(i,j,e),a in zip(labels,sol)if a]
  break
 (root/'simple-discriminant-current-results.json').write_text(json.dumps(report,indent=2))
 print(json.dumps({k:v for k,v in report.items()if k!='candidate'},indent=2),flush=True)

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--prime',type=int,default=1009)
 parser.add_argument('--initial-points',type=int,default=600);args=parser.parse_args();run(args.prime,args.initial_points)
