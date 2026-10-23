"""Add three nonexact conic-log residue classes to the merged simple poles.

No degree extension: compact4+infinity currents retain the H,+,- simple poles.
For s=-3z/2,L=H+sC and g=x,y,z, the rational finite-pole current
V=(grad L-3L grad z/z) cross grad(log g) carries K_g * M_H e0,
K_g=V(C)-2C V(z)/z, after the explicit exact endpoint correction.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
import merged_simple_poles as base

root=Path(__file__).parent

def log_columns(points,p,source):
 x,y,z=points.T
 power=lambda ar,n:np.array([pow(int(a),n,p)for a in ar],dtype=np.int64)
 inv=lambda ar:np.array([pow(int(a),-1,p)for a in ar],dtype=np.int64)
 i2=pow(2,-1,p);i3=pow(3,-1,p);i4=pow(4,-1,p)
 ix,iy,iz=inv(x),inv(y),inv(z)
 L=(1+power(x,6)+power(y,6)+power(z,6)-3*i4*power(x,3)%p*power(z,2))%p
 C=(power(x,3)*z*i2+x*y*i3)%p
 lam=[(6*power(x,5)-9*i4*power(x,2)%p*power(z,2))%p,
      6*power(y,5)%p,
      (6*power(z,5)-3*i2*power(x,3)%p*z-3*L*iz)%p]
 dc=[(3*i2*power(x,2)%p*z+y*i3)%p,x*i3%p,power(x,3)*i2%p]
 zero=np.zeros(len(points),dtype=np.int64)
 vectors=[(zero,lam[2]*ix%p,-lam[1]*ix%p),
          (-lam[2]*iy%p,zero,lam[0]*iy%p),
          (lam[1]*iz%p,-lam[0]*iz%p,zero)]
 src=source.reshape((-1,5))
 # source = -y^3 M_H e0/6 in the exact original-coordinate orientation.
 mh=src*((-6*inv(power(y,3)))%p)[:,None]%p
 columns=[]
 for V in vectors:
  K=(sum(V[i]*dc[i]%p for i in range(3))-2*C*V[2]%p*iz)%p
  columns.append((mh*K[:,None]%p).reshape(-1))
 return np.column_stack(columns)

def matrix_for(labels,points,p):
 mat,rhs=base.matrix_for(labels,points,p)
 return np.column_stack((mat,log_columns(points,p,rhs))),rhs

def run(p,initial_count):
 labels=base.labels_for();n=len(labels)+3
 counts=[initial_count]if initial_count>=n else[initial_count,n+12]
 report={'prime':p,'unknowns':n,'compact_unknowns':len(labels),
         'additional_classes':['dlog r wedge dlog x','dlog r wedge dlog y','dlog r wedge dlog z'],
         'source':'-y^3 MH e0/6','stages':[]}
 for stage,count in enumerate(counts):
  print({'stage':stage,'generic_points':count,'building_matrix':True},flush=True)
  points=base.q.sample_points(count,p,728193+stage)
  mat,rhs=matrix_for(labels,points,p)
  start=time.monotonic();rank,sol=base.solve_mod(mat,rhs,p,progress=True)
  rec={'generic_points':count,'rows':len(rhs),'rank':rank,
       'consistent':sol is not None,'solve_seconds':time.monotonic()-start}
  report['stages'].append(rec)
  if sol is None:
   report['status']='inconsistent sampled system; no current in this modular merged-plus-log ansatz';break
  if count<n:
   print('Partial consistency is not a candidate; increasing to full point count.',flush=True);continue
  points=base.q.sample_points(600,p,473918);mat,rhs=matrix_for(labels,points,p)
  residual=(mat@sol-rhs)%p;rec['fresh_nonzero_residuals']=int(np.count_nonzero(residual))
  if np.any(residual):
   report['status']='sample interpolation rejected by fresh points; no candidate';break
  report['status']='modular candidate requires exact reconstruction and full polynomial verification'
  report['compact_candidate']=[{'denominator':name,'i':i,'j':base.basis[j],
      'monomial':e,'coefficient':int(a)}for(name,i,j,e),a in zip(labels,sol[:-3])if a]
  report['log_candidate']=[int(a)for a in sol[-3:]]
  break
 (root/'merged-log-residue-results.json').write_text(json.dumps(report,indent=2))
 print(json.dumps({k:v for k,v in report.items()if'candidate'not in k},indent=2),flush=True)

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--prime',type=int,default=1009)
 parser.add_argument('--initial-points',type=int,default=1436);args=parser.parse_args()
 run(args.prime,args.initial_points)
