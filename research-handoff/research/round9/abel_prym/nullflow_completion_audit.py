"""Independent FLINT-series replay of the restricted boundary completion test."""
from pathlib import Path
import json,time,sys
from flint import nmod_poly
HERE=Path(__file__).parent;start=time.monotonic();ref=json.load(open(HERE.parent/'open_curve'/'nullflow_completion.json'));p=ref['prime'];N=4
sys.path.insert(0,str(HERE.parent.parent/'round10'/'horizontal5'))
from physical_search import OpenModel,qmod
class F:
 def __init__(self,a=0):self.f=a.f if isinstance(a,F)else (a if isinstance(a,nmod_poly)else nmod_poly(a if isinstance(a,list)else[a],p));self.f=self.f.truncate(N)
 def __add__(a,b):return F(a.f+F(b).f)
 __radd__=__add__
 def __neg__(a):return F(-a.f)
 def __sub__(a,b):return a+-F(b)
 def __rsub__(a,b):return F(b)+-a
 def __mul__(a,b):return F((a.f*F(b).f).truncate(N))
 __rmul__=__mul__
 def __pow__(a,n):return F(a.f.inverse_series_trunc(N)).__pow__(-n)if n<0 else F(a.f.pow_trunc(n,N))
 def __truediv__(a,b):return a*F(b)**-1
 def __rtruediv__(a,b):return F(b)*a**-1
 def der(a):return F(a.f.derivative())
 def coef(a,n):return int(a.f[n])
 def coefs(a):return[a.coef(i)for i in range(N)]
def ev(poly,args):
 out=F(0)
 for ex,c in poly.d:
  val=F(c)
  for arg,k in zip(args,ex):val*=arg**k
  out+=val
 return out
pair=lambda pp,args:ev(pp[0],args)/ev(pp[1],args)
model=OpenModel(p,str(HERE.parent.parent/'round10'/'horizontal5'/'rank5_connection.pickle'));c=qmod('5/7',p)
def physical(a,b,v):
 E=1+a*v;B=b*E;P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R
 return[(27*P*S*S-9*Q*R*S+2*R**3)/(3*A*A),(3*S*Q-R*R)/(B*A),3*B**3/A],B*R/A,dict(a=a,b=b,v=v,A=A,E=E,S=S)
def delta(par):
 L,r,x=par;return[x*((c*c-10*r)*L+4*r*r),x*r*(c*c-5*r)-18*L+9*r,-x*((c*c+5*r)*x+27)]
records=[]
for old in ref['records']:
 ph=[F(q)for q in old['physical_third_jets']];par,z,polys=physical(*ph)
 assert[q.coefs()for q in par]==old['canonical_third_jets']
 ff=delta(par)
 for q,f in zip(par,ff):assert all((q.der()-f).coef(i)==0 for i in range(3))
 mark=ev(model.N1,par+[z])/ev(model.N0,par+[z]);assert mark.coefs()==old['mark_third_jet']
 source=-pair(model.proper.conn[1][5],par)+2*z*pair(model.proper.conn[1][2],par)-z*z*pair(model.proper.conn[0][2],par)
 L,r,x=par;A=c*(1+mark);B=L+r*mark+mark**3/x;disc=A*A-4*B;K=r*(5*mark+4)+3*mark*(2*mark+3)/x;V=mark.der()/x+K;norm=V*V-c*A*V+c*c*B
 seed=[-7*source*disc*c*B/(2*norm),-7*source*disc*V/(2*norm)];ker=[B*(2*V-c*A),A*V-2*c*B]
 R=[[sum((ff[k]*pair(model.conn[name][i+3][j+3],par+[mark])for k,name in enumerate(('L','r','x'))),F(0))+mark.der()*pair(model.conn['s'][i+3][j+3],par+[mark])for j in range(2)]for i in range(2)]
 h=3*polys['a'].der()/polys['a']+qmod('13/3',p)*polys['A'].der()/polys['A']-5*polys['b'].der()/polys['b']-4*polys['E'].der()/polys['E']-qmod('4/3',p)*polys['S'].der()/polys['S']
 dlt=ev(model.proper.polys['Delta47'],ph);h-=dlt.der()/dlt+30*r*x+18
 def close(Z):return[Z[j].der()+h*Z[j]+sum((R[i][j]*Z[i]for i in range(2)),F(0))for j in range(2)]
 CZ,CP=close(seed),close(ker)
 determinant=CP[0]*ker[1]-CP[1]*ker[0]
 T=(-CZ[0]*ker[1]+CZ[1]*ker[0])/determinant
 forced=(-CP[0]*CZ[1]+CP[1]*CZ[0])/determinant
 defect=(T.coef(1)-forced.coef(0))%p
 assert defect==old['closedness_compatibility_defect'] and defect!=0
 assert T.coef(0)==old['T_forced'] and T.coef(1)==old['deltaT_actual'] and forced.coef(0)==old['deltaT_forced']
 records.append({'point':old['point'],'canonical_ODE_through_order2':True,'physical_map_through_order3':True,'compatibility_defect':defect})
result={'prime':p,'records':records,'all_four_replays_pass':True,'independent_engine':'Native FLINT truncated univariate polynomial arithmetic; no nullflow_completion.J or its inverse/map solver is imported. Supplied physical trajectories verified against the physical rational map and canonical ODE through all needed orders.','jet_order_reason':'Z and P depend on mark prime. T algebraic and its derivative use closures only through order1, so mark/physical trajectories through order3 suffice; missing order4 never enters the checked coefficients.','convention_audit':'eta-matched seed pairs to source, kernel pairs to zero; weighted divergence is delta(logH)-30*r*x-18; 2x2 forcedT/forcedTprime signs checked by Cseed+T*Ckernel+Tprime*kernel=0.','scope':'Seals only the stated boundary current restricted to the Prym-nullflow and carrying all eta source, with proper corrections eta-free. Transverse boundary components and general rank5 currents remain open.','seconds':time.monotonic()-start}
(HERE/'nullflow_completion_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
