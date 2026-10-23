"""Exact physical firstjets of the pencil-normal frame (N0p,N1p,v).

The coefficient polynomials are the canceled canonical effective-point ratio
from round9/abel_prym/effective_physical.pickle, keyT_effective_canonical.
No source-current sweep is performed here.
"""
from pathlib import Path
import sys,pickle,json,time,hashlib
HERE=Path(__file__).parent
sys.path.insert(0,'/workspace/research/round10/horizontal5')
from physical_search import Jet,PolyND,qmod
from jet2 import Jet2,evaluate
SOURCE=Path('/workspace/research/round9/abel_prym/effective_physical.pickle')
class PencilFrame:
 def __init__(self,p):
  self.p=p;raw=pickle.loads(SOURCE.read_bytes())['T_effective_canonical']
  self.raw={'N0p':raw['den'],'N1p':raw['num']}
  self.polys=[PolyND(raw[key],p)for key in ['den','num']]
 def point(self,point):
  p=self.p;Jet.p=p;Jet2.p=p
  args=[Jet2(point[i],[int(i==j)for j in range(3)])for i in range(3)]
  vals=[evaluate(poly,args)for poly in self.polys];F,G=[Jet(z.x,z.d)for z in vals]
  dF=[Jet(vals[0].d[i],vals[0].h[i])for i in range(3)];dG=[Jet(vals[1].d[i],vals[1].h[i])for i in range(3)]
  Jab=dF[0]*dG[1]-dF[1]*dG[0]
  VF=[dG[1]/Jab,-dG[0]/Jab,Jet(0)]
  VG=[-dF[1]/Jab,dF[0]/Jab,Jet(0)]
  VQ=[(dF[1]*dG[2]-dF[2]*dG[1])/Jab,(dF[2]*dG[0]-dF[0]*dG[2])/Jab,Jet(1)]
  dual=[VF,VG,VQ]
  # These include the gradients of every product, not only point values.
  gradients=[dF,dG,[Jet(0),Jet(0),Jet(1)]]
  for i,gg in enumerate(gradients):
   for j,V in enumerate(dual):
    q=sum((a*b for a,b in zip(gg,V)),Jet(0))
    assert q.x==int(i==j) and not any(q.d)
  E=[F*VF[i]+G*VG[i]for i in range(3)]
  for scalar,gradient in zip([F,G],[dF,dG]):
   q=sum((a*b for a,b in zip(E,gradient)),Jet(0));assert(q.x,q.d)==(scalar.x,scalar.d)
  fields={'dual_N0':VF,'dual_N1':VG,'dual_v':VQ,'Euler':E}
  if F.x:
   fields['radial']= [e/(F*F)for e in E]
   fields['curve_s']= [F*v for v in VG]
  return {'pt':list(point),'N0p':F,'N1p':G,'Jab':Jab,'scalar_second_jets':vals,'fields':fields}

def holdout(data):
 return {'pt':data['pt'],'N0p':{'value':data['N0p'].x,'gradient':data['N0p'].d},'N1p':{'value':data['N1p'].x,'gradient':data['N1p'].d},'Jab':{'value':data['Jab'].x,'gradient':data['Jab'].d},'fields':{name:[{'value':z.x,'gradient':z.d}for z in field]for name,field in data['fields'].items()}}
if __name__=='__main__':
 start=time.monotonic();model=PencilFrame(1000003);records=[holdout(model.point(pt))for pt in [[1,2,3],[2,1,3],[2,3,1],[3,4,2]]]
 cone=PencilFrame(101).point([41,25,1]);assert cone['N0p'].x==cone['N1p'].x==0
 print('CONEPOINT',cone['Jab'].x,flush=True)
 packet={'variables':('a','b','v'),'N0p':model.raw['N0p'],'N1p':model.raw['N1p'],'formula':'Jab=N0_a*N1_b−N0_b*N1_a; VF=(N1_b,−N1_a,0)/Jab; VG=(−N0_b,N0_a,0)/Jab; VQ=((N0_b*N1_v−N0_v*N1_b),(N0_v*N1_a−N0_a*N1_v),Jab)/Jab; E=N0*VF+N1*VG; radial=E/N0²; curve_s=N0*VG.','normalization':'N0p=den,N1p=num of canceled T_effective_canonical ratio, preserving its exact rational coefficient normalization.'}
 (HERE/'frame.pickle').write_bytes(pickle.dumps(packet))
 result={'prime':1000003,'holdouts':records,'cone_good_point':{'prime':101,'point':[41,25,1],'N0p':0,'N1p':0,'Jab':cone['Jab'].x},'all_dual_and_Euler_firstjet_identities':True,'normalization':packet['normalization'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'seconds':time.monotonic()-start}
 (HERE/'frame_holdouts.json').write_text(json.dumps(result,indent=2,default=int)+'\n');print(json.dumps({'seconds':time.monotonic()-start,'cone_Jab':cone['Jab'].x,'all_dual_and_Euler_firstjet_identities':True},indent=2))
