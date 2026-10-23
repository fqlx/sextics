"""Independent ordinary-rational-oneform audit of the eight open GM rows."""
from pathlib import Path
import pickle,json,time,random
from functools import lru_cache
import sympy as sy
HERE=Path(__file__).parent;start=time.monotonic();prime=1000003
proper=pickle.load(open(HERE.parent/'cyclic_full'/'global_eta_complete.pickle','rb'))
packet=pickle.load(open(HERE.parent/'open_curve'/'boundary_native.pickle','rb'))
W,h,T,L,r,x=proper['symbols'];ss=sy.Symbol('s');C=proper['curve'];Ct=sy.diff(C,T);Ctt=sy.diff(C,T,2);CW=sy.diff(C,W)
class D:
 def __init__(self,a=0,b=0):
  if isinstance(a,D):self.a,self.b=a.a,a.b
  else:self.a,self.b=int(a)%prime,int(b)%prime
 def __add__(a,b):b=D(b);return D(a.a+b.a,a.b+b.b)
 __radd__=__add__
 def __neg__(a):return D(-a.a,-a.b)
 def __sub__(a,b):return a+-D(b)
 def __rsub__(a,b):return D(b)+-a
 def __mul__(a,b):b=D(b);return D(a.a*b.a,a.a*b.b+a.b*b.a)
 __rmul__=__mul__
 def __pow__(a,n):
  if n==0:return D(1)
  return D(pow(a.a,n,prime),n*pow(a.a,n-1,prime)*a.b)
 def __truediv__(a,b):return a*D(b)**-1
 def __rtruediv__(a,b):return D(b)*a**-1

def evaluator(vals):
 @lru_cache(None)
 def ev(e):
  if e.is_Rational:return D(int(e.p))/int(e.q)
  if e.is_Symbol:return vals[e]
  if e.is_Add:return sum((ev(q)for q in e.args),D(0))
  if e.is_Mul:
   v=D(1)
   for q in e.args:v*=ev(q)
   return v
  if e.is_Pow:return ev(e.base)**int(e.exp)
  raise TypeError(e)
 return ev

def rat(ev,payload):
 def poly(dd):
  out=D(0)
  for ex,coeff in dd.items():
   cc=sy.Rational(coeff);v=D(int(cc.p))/int(cc.q)
   for sym,k in zip((L,r,x,ss),ex):v*=ev(sym)**k
   out+=v
  return out
 return poly(payload['numerator'])/poly(payload['denominator'])
def forms(ev):
 result=[]
 for P,pole in zip(proper['basis'],proper['basis_pole_orders']):result.append(ev(P)/ev(Ct)if pole==1 else (ev(sy.diff(P,T))*ev(Ct)-ev(P)*ev(Ctt))/ev(Ct)**3)
 for j in(0,1):result.append(ev(W)**(3*j)/((ev(T)-ev(ss))*ev(Ct)))
 return result

def F(ev,direction,j):
 val=D(0)
 for coeff,(component,ex)in zip(packet['primitive_coefficients'][direction][j],packet['primitive_labels']):
  if component not in(0,1):continue
  val+=(-1 if component==1 else 1)*rat(ev,coeff)*ev(W)**(ex[0]+int(component==1))*ev(T)**ex[2]
 return val/((ev(T)-ev(ss))*ev(Ct))
rng=random.Random(719);records=[];checks=0
while len(records)<10:
 ww,tt,rr,xx,ee=[rng.randrange(1,prime)for _ in range(5)];cc=5*pow(7,-1,prime)%prime
 ll=(-ww**6-cc*(1+tt)*ww**3-rr*tt-tt**3*pow(xx,-1,prime))%prime
 values={W:ww,h:1,T:tt,L:ll,r:rr,x:xx,ss:ee};ev=evaluator({q:D(z)for q,z in values.items()})
 try:
  assert ev(C).a==0
  ct,cw=ev(Ct).a,ev(CW).a;betas=[q.a for q in forms(ev)]
  fw=evaluator({q:D(z,1 if q==W else -cw*pow(ct,-1,prime)if q==T else 0)for q,z in values.items()})
  for name in('L','r','x','s'):
   sym={'L':L,'r':r,'x':x,'s':ss}[name];ci=ev(sy.diff(C,sym)).a
   fi=evaluator({q:D(z,1 if q==sym else -ci*pow(ct,-1,prime)if q==T else 0)for q,z in values.items()})
   lhs=forms(fi)
   for j in(0,1):
    connection=sum(rat(ev,k).a*z for k,z in zip(packet['connection_boundary'][name][j],betas))%prime
    exact=F(fw,name,j).b
    assert(lhs[j+3].b-connection-exact)%prime==0,(values,name,j,lhs[j+3].b,connection,exact)
    checks+=1
  records.append({'W':ww,'T':tt,'L':ll,'r':rr,'x':xx,'s':ee})
 except ZeroDivisionError:continue
result={'prime':prime,'points':records,'ordinary_boundary_derivative_checks':checks,'all_pass':True,'primitive_sign':'PLUS (QW-W*Qh)/((T-s)*Ct)','method':'Dual-number differentiation of ordinary rational oneforms with t_i=-Ci/Ct and t_W=-CW/Ct. Neither native coefficient matrix nor its exact19-row verification is imported. Uses literal clean eta_new pole2 representative.','scope':'Independent sign/normalization audit of all8 boundary rows and their exact primitives; no source solution or unbounded exclusion.','seconds':time.monotonic()-start}
(HERE/'rank5_ordinary_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
