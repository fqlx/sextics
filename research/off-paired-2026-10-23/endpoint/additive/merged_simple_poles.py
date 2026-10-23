"""Focused additive H,+,- simple-pole current for exact physical source.

Original chart x=X1,y=Y0,z=Y1, compact4 plus infinityomega2.
The current is P/H+Q/(2C3+27H2)+R/(2C3-27H2), with degree/characters
as in the individual fixed-pole systems. This tests coupled pole cancellation.
"""
import sys,numpy as np,json,time,argparse
from pathlib import Path
root=Path(__file__).parent;sys.path.insert(0,str(root.parent))
import two_pole_infinity_current_search as q
from block_modular import solve_mod
positions=[0,1,6,2,3];basis=[0,1,2,3,4];weights=[2,1,3]

def labels_for():
 labels=[]
 for name,degree,deltas in [('H',6,[0]),('plus',12,[0,3]),('minus',12,[0,3])]:
  for i in range(3):
   for j,index in enumerate(basis):
    for delta in deltas:
     for e in q.monomials(degree+1-2*index,(3+delta+weights[i]-3*index)%6):labels.append((name,i,j,e))
 return labels

def denominator_data(points,p):
 x,y,z=points.T;pw=lambda arr,n:np.array([pow(int(a),n,p)for a in arr],dtype=np.int64);i2=pow(2,-1,p);i3=pow(3,-1,p)
 h=(1+pw(x,6)+pw(y,6)+pw(z,6)+x*y%p*z*i2)%p;c=(pw(x,3)*z*i2+x*y*i3)%p
 dh=[(6*pw(x,5)+y*z*i2)%p,(6*pw(y,5)+x*z*i2)%p,(6*pw(z,5)+x*y*i2)%p]
 dc=[(3*pw(x,2)*z*i2+y*i3)%p,x*i3%p,pw(x,3)*i2%p]
 Ds={'H':h,'plus':(2*c*c%p*c+27*h*h)%p,'minus':(2*c*c%p*c-27*h*h)%p}
 out={}
 for name in Ds:
  dd=Ds[name];assert np.all(dd);inv=np.array([pow(int(a),-1,p)for a in dd],dtype=np.int64)
  grad=dh if name=='H' else[(6*c*c%p*dc[i]+(54 if name=='plus' else -54)*h*dh[i])%p for i in range(3)]
  out[name]=(inv,[di*inv%p for di in grad])
 return out

def matrix_for(labels,points,p):
 bigbi,bigsource=q.connection(points,p);bi=[a[positions][:,positions]for a in bigbi];source=bigsource[positions]
 ds=denominator_data(points,p);mat=np.zeros((len(points)*5,len(labels)),dtype=np.int64);mons={}
 for col,(name,i,j,e)in enumerate(labels):
  if e not in mons:mons[e]=q.poly_evaluate([(e,1)],points.T,p)
  mm=mons[e];inv,dlog=ds[name]
  for k in range(5):mat[k::5,col]=mm*bi[i][k,j]%p*inv%p
  derivative=np.zeros(len(points),dtype=np.int64)
  if e[i]:
   ee=tuple(a-(1 if h==i else 0)for h,a in enumerate(e))
   if ee not in mons:mons[ee]=q.poly_evaluate([(ee,1)],points.T,p)
   derivative=e[i]*mons[ee]%p
  mat[j::5,col]=(mat[j::5,col]+(derivative-mm*dlog[i])%p*inv)%p
 return mat,source.T.reshape(-1)

def run(p,initial_count):
 labels=labels_for();n=len(labels);assert n==2740
 counts=[initial_count] if initial_count>=n else[initial_count,n+12]
 report={'prime':p,'unknowns':n,'basis':basis,'families':{'H':sum(a[0]=='H'for a in labels),'plus':sum(a[0]=='plus'for a in labels),'minus':sum(a[0]=='minus'for a in labels)},'source':'-y^3 MH e0/6','stages':[]}
 for stage,count in enumerate(counts):
  print({'stage':stage,'generic_points':count,'building_matrix':True},flush=True)
  points=q.sample_points(count,p,728193+stage);mat,rhs=matrix_for(labels,points,p)
  start=time.monotonic();rank,sol=solve_mod(mat,rhs,p,progress=True)
  rec={'generic_points':count,'rows':len(rhs),'rank':rank,'consistent':sol is not None,'solve_seconds':time.monotonic()-start};report['stages'].append(rec)
  if sol is None:
   report['status']='inconsistent sampled system; no current in this modular additive ansatz';break
  if count<n:
   print('Partial consistency is not a candidate; increasing to full point count.',flush=True);continue
  fresh=q.sample_points(600,p,473918);fm,fr=matrix_for(labels,fresh,p);res=(fm@sol-fr)%p
  rec['fresh_nonzero_residuals']=int(np.count_nonzero(res))
  if np.any(res):
   report['status']='sample interpolation rejected by fresh points; no candidate';break
  report['status']='modular candidate requires exact rational reconstruction and full polynomial verification'
  report['candidate']=[{'denominator':name,'i':i,'j':basis[j],'monomial':e,'coefficient':int(a)}for(name,i,j,e),a in zip(labels,sol)if a]
  break
 (root/'merged-simple-poles-results.json').write_text(json.dumps(report,indent=2));print(json.dumps({a:b for a,b in report.items()if a!='candidate'},indent=2),flush=True)
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--prime',type=int,default=1009);parser.add_argument('--initial-points',type=int,default=1434);args=parser.parse_args();run(args.prime,args.initial_points)
