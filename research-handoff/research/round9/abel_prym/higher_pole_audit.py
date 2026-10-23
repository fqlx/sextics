"""Direct moving-curve derivative audit of higher-pole absolute primitives.

For beta=Res(P Omega/C^2), ordinary representative is
  ((P_t C_t-P C_tt)/C_t^3) dW.
The complete PLUS primitive is u8/Ct+(u14_t Ct-u14 Ctt)/Ct^3.
All derivatives below are dual-number derivatives of these ordinary rational
functions, with t_z=-C_z/C_t and t_W=-C_W/C_t on the moving curve.
"""
import pickle,json,random,time
from pathlib import Path
from functools import lru_cache
import sympy as s
HERE=Path(__file__).parent;start=time.monotonic();p=1000003;c=5*pow(7,-1,p)%p
class D:
 def __init__(self,a=0,b=0):
  if isinstance(a,D):self.a,self.b=a.a,a.b
  else:self.a,self.b=int(a)%p,int(b)%p
 def __add__(a,b):b=D(b);return D(a.a+b.a,a.b+b.b)
 __radd__=__add__
 def __neg__(a):return D(-a.a,-a.b)
 def __sub__(a,b):return a+-D(b)
 def __rsub__(a,b):return D(b)+-a
 def __mul__(a,b):b=D(b);return D(a.a*b.a,a.a*b.b+a.b*b.a)
 __rmul__=__mul__
 def __pow__(a,n):
  if n==0:return D(1)
  return D(pow(a.a,n,p),n*pow(a.a,n-1,p)*a.b)
 def __truediv__(a,b):return a*D(b)**-1
 def __rtruediv__(a,b):return D(b)*a**-1

def evaluate(values):
 @lru_cache(None)
 def ev(e):
  if e.is_Rational:return D(int(e.p))/int(e.q)
  if e.is_Symbol:return values[e]
  if e.is_Add:return sum((ev(q)for q in e.args),D(0))
  if e.is_Mul:
   z=D(1)
   for q in e.args:z*=ev(q)
   return z
  if e.is_Pow:return ev(e.base)**int(e.exp)
  raise TypeError(e)
 return ev
blocks={n:pickle.load(open(HERE.parent/'cyclic_full'/f'{n}_fast.pickle','rb'))for n in('actual','conjugate')}
W,h,t,L,r,x=blocks['actual']['symbols'];C=blocks['actual']['curve'];Ct=s.diff(C,t);Ctt=s.diff(C,t,2);CW=s.diff(C,W)
def relform(data,idx,ev):
 P=data['basis'][idx]
 return ev(P)/ev(Ct) if data['basis_pole_orders'][idx]==1 else (ev(s.diff(P,t))*ev(Ct)-ev(P)*ev(Ctt))/ev(Ct)**3

def uj(data,pp,degree,ev,derivative=False):
 raw=pp[f'Q{degree}_raw'];den=pp[f'Q{degree}_denominator'];out=D(0)
 if raw is None:return out
 for coeff,(component,ex)in zip(raw,data[f'lab{degree}']):
  if component not in(0,1)or coeff==0:continue
  ew=ex[0]+int(component==1);et=ex[2]
  z=(-1 if component==1 else 1)*ev(coeff)*ev(W)**ew
  if derivative:
   if not et:continue
   z*=et*ev(t)**(et-1)
  else:z*=ev(t)**et
  out+=z
 return out/ev(den)
def primitive(data,idx,name,ev):
 pp=data['primitives'][name][idx]
 out=uj(data,pp,8,ev)/ev(Ct)
 if pp['Q14_raw']is not None:out+=(uj(data,pp,14,ev,True)*ev(Ct)-uj(data,pp,14,ev)*ev(Ctt))/ev(Ct)**3
 return out
rng=random.Random(957);records=[];counts={'holomorphic_rows':0,'meromorphic_rows':0}
while len(records)<8:
 ww,tt,rr,xx=[rng.randrange(1,p)for _ in range(4)]
 ll=(-ww**6-c*(1+tt)*ww**3-rr*tt-tt**3*pow(xx,-1,p))%p
 vals={W:ww,h:1,t:tt,L:ll,r:rr,x:xx};ev0=evaluate({k:D(z)for k,z in vals.items()})
 try:
  assert ev0(C).a==0
  ct,cw=ev0(Ct).a,ev0(CW).a
  fw=evaluate({k:D(z,1 if k==W else -cw*pow(ct,-1,p)if k==t else 0)for k,z in vals.items()})
  for name,data in blocks.items():
   for idx in range(3):
    betas=[relform(data,j,ev0).a for j in range(3)]
    for direction in('L','r','x'):
     sym={'L':L,'r':r,'x':x}[direction];cz=ev0(s.diff(C,sym)).a
     fz=evaluate({k:D(z,1 if k==sym else -cz*pow(ct,-1,p)if k==t else 0)for k,z in vals.items()})
     lhs=relform(data,idx,fz).b
     nf=sum(ev0(data['connection'][direction][idx,j]).a*betas[j]for j in range(3))%p
     exact=primitive(data,idx,direction,fw).b
     assert(lhs-nf-exact)%p==0,(vals,name,idx,direction,lhs,nf,exact)
     counts['holomorphic_rows'if idx<len(data['hol'])else'meromorphic_rows']+=1
  records.append({'W':ww,'T':tt,'L':ll,'r':rr,'x':xx,'Ct':ct})
 except ZeroDivisionError:continue
result={'prime':p,'records':records,'checks':counts,'higher_pole_primitive':'F=u8/Ct+(u14_t*Ct-u14*Ctt)/Ct^3; all stored denominators included; no factor 2.','relative_pole2_representative':'(P_t*Ct-P*Ctt)/Ct^3*dW','all_moving_curve_identities_pass':True,'method':'Independent dual-number derivatives of ordinary rational one-forms. Tested d_z beta_i=sum_j N_ij beta_j+d_f F_i on C=0 using t_z=-Cz/Ct and t_W=-CW/Ct.','scope':'This establishes the evaluator convention for extending marked trace currents to all six de Rham basis forms. It does not solve the current PDE or serve the target.','seconds':time.monotonic()-start}
(HERE/'higher_pole_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
