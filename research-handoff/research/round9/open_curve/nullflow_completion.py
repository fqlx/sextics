"""Try the full eta-matched pure-nullflow boundary current via a forced correction.
Univariate formal trajectories retain all third physical jets exactly mod p.
"""
from pathlib import Path
import sys,pickle,json,time
HERE=Path(__file__).parent;sys.path.insert(0,'/workspace/research/round10/horizontal5')
from physical_search import OpenModel,Jet,qmod,dot
start=time.monotonic();p=1000003;order=3
class J:
 def __init__(a,x=0):a.c=[int(x)%p]+[0]*order
 @staticmethod
 def coerce(x):return x if isinstance(x,J)else J(x)
 def __add__(a,b):
  b=a.coerce(b);o=J();o.c=[(x+y)%p for x,y in zip(a.c,b.c)];return o
 __radd__=__add__
 def __neg__(a):o=J();o.c=[-x%p for x in a.c];return o
 def __sub__(a,b):return a+-a.coerce(b)
 def __rsub__(a,b):return a.coerce(b)+-a
 def __mul__(a,b):
  b=a.coerce(b);o=J();o.c=[sum(a.c[i]*b.c[k-i]for i in range(k+1))%p for k in range(order+1)];return o
 __rmul__=__mul__
 def inv(a):
  o=J(pow(a.c[0],-1,p))
  for k in range(1,order+1):o.c[k]=-sum(a.c[i]*o.c[k-i]for i in range(1,k+1))*o.c[0]%p
  return o
 def __truediv__(a,b):return a*a.coerce(b).inv()
 def __rtruediv__(a,b):return a.coerce(b)*a.inv()
 def __pow__(a,n):
  if n<0:return a.inv()**(-n)
  out=J(1);v=a
  while n:
   if n&1:out=out*v
   n//=2
   if n:v=v*v
  return out
 def der(a):o=J();o.c=[(k+1)*a.c[k+1]%p for k in range(order)]+[0];return o

def ev(poly,args):
 maxima=[max((e[i]for e,c in poly.d),default=0)for i in range(len(args))];powers=[]
 for a,n in zip(args,maxima):
  pp=[J(1)]
  for i in range(n):pp.append(pp[-1]*a)
  powers.append(pp)
 out=J()
 for e,c in poly.d:
  v=J(c)
  for i,k in enumerate(e):v=v*powers[i][k]
  out=out+v
 return out

def pair(f,args):return ev(f[0],args)/ev(f[1],args)
model=OpenModel(p,'/workspace/research/round10/horizontal5/rank5_connection.pickle');c=qmod('5/7',p)
def physical(args):
 a,b,v=args;E=1+a*v;B=b*E;P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R
 L=(27*P*S*S-9*Q*R*S+2*R**3)/(3*A*A);r=(3*S*Q-R*R)/(B*A);x=3*B**3/A;z=B*R/A
 return [L,r,x],z,dict(a=a,b=b,v=v,A=A,E=E,S=S)
def flow(par):
 L,r,x=par;return[x*((c*c-10*r)*L+4*r*r),x*r*(c*c-5*r)-18*L+9*r,-x*((c*c+5*r)*x+27)]
records=[]
for pt in [[1,2,3],[2,1,3],[2,3,1],[3,4,2]]:
 d=model.point(pt);canonical=[J(v)for v in d['pars']]
 for k in range(order):
  ff=flow(canonical)
  for j in range(3):canonical[j].c[k+1]=ff[j].c[k]*pow(k+1,-1,p)%p
 ph=[J(v)for v in pt]
 for k in range(1,order+1):
  got,_,_=physical(ph);res=[(canonical[j].c[k]-got[j].c[k])%p for j in range(3)]
  for a in range(3):ph[a].c[k]=sum(d['fields'][j][a]*res[j]for j in range(3))%p
 par,z,factors=physical(ph)
 assert all(a.c==b.c for a,b in zip(par,canonical))
 L,r,x=par;mark=ev(model.N1,par+[z])/ev(model.N0,par+[z]);assert mark.c[0]==d['s'].x
 source=-pair(model.proper.conn[1][5],par)+2*z*pair(model.proper.conn[1][2],par)-z*z*pair(model.proper.conn[0][2],par)
 assert source.c[0]==d['rhs'][2]
 A=c*(1+mark);B=L+r*mark+mark**3/x;Delta=A*A-4*B;K=r*(5*mark+4)+3*mark*(2*mark+3)/x;D0=mark.der()/x+K;NF=D0*D0-c*A*D0+c*c*B
 Z=[-7*source*Delta*c*B/(2*NF),-7*source*Delta*D0/(2*NF)]
 P=[B*(2*D0-c*A),A*D0-2*c*B]
 ff=flow(par);NN=[[J()for j in range(2)]for i in range(2)]
 for i in range(2):
  for j in range(2):
   NN[i][j]=sum((ff[k]*pair(model.conn[name][i+3][j+3],par+[mark])for k,name in enumerate(['L','r','x'])),J())+mark.der()*pair(model.conn['s'][i+3][j+3],par+[mark])
 h=3*factors['a'].der()/factors['a']+qmod('13/3',p)*factors['A'].der()/factors['A']-5*factors['b'].der()/factors['b']-4*factors['E'].der()/factors['E']-qmod('4/3',p)*factors['S'].der()/factors['S']
 DD=ev(model.proper.polys['Delta47'],ph);h=h-DD.der()/DD-30*r*x-18
 def closure(V):return[V[j].der()+h*V[j]+sum((NN[i][j]*V[i]for i in range(2)),J())for j in range(2)]
 CZ,CP=closure(Z),closure(P)
 det=P[0]*CP[1]-P[1]*CP[0]
 if not det.c[0]:records.append({'point':pt,'generic_completion_determinant':0});continue
 T=(-P[0]*CZ[1]+P[1]*CZ[0])/det
 dTforced=(-CZ[0]*CP[1]+CZ[1]*CP[0])/det
 defect=(T.c[1]-dTforced.c[0])%p
 records.append({'point':pt,'canonical_third_jets':[q.c for q in par],'physical_third_jets':[q.c for q in ph],'mark_third_jet':mark.c,'closure_seed':[q.c[0]for q in CZ],'completion_determinant':det.c[0],'T_forced':T.c[0],'deltaT_actual':T.c[1],'deltaT_forced':dTforced.c[0],'closedness_compatibility_defect':defect,'passes':not defect})
out={'prime':p,'records':records,'scope':'The full eta-matched boundary current restricted to the Prym-nullflow direction only. A nonzero rational compatibility defect excludes that shape; general boundary2forms with transverse components and proper-current corrections remain open.','seconds':time.monotonic()-start}
(HERE/'nullflow_completion.json').write_text(json.dumps(out,indent=2,default=int)+'\n');print(json.dumps(out,indent=2,default=int))
