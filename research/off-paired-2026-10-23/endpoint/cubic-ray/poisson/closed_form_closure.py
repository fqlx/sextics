"""Small closed rational two-form closure for the actual full-G36 source.

Each column is a closed rational 2-form, optionally trace-free projected.
There are no unknown coordinate-polynomial coefficients or degree grids.
Any hit gives the actual primitive theta wedge beta, subject to exact lifting.
"""
import sys,json,itertools
from pathlib import Path
import sympy as S
import numpy as np
root=Path(__file__).parent
sys.path.insert(0,str(root.parent));sys.path.insert(0,str(root.parents[1]/'additive'))
from finite_connection import H,B,C,D,MH,MB,MC
from block_modular import solve_mod

z,U,K,t=S.symbols('z U K t');qs=[z,U,K,t]
phys=[1+z**2+t,U/2+K/3+z*U*K/2,z**-2+U**6+K**6/t]
P=D.subs(dict(zip([H,B,C],phys)))
hs={'z':z,'U':U,'K':K,'t':t,'H':phys[0],'B':phys[1],'C':phys[2],
    'D':P,'a=1+zK':1+z*K,'b=2+3zU':2+3*z*U,
    'H0=1+z2':1+z**2,'C0=z^-2+U6':z**-2+U**6,
    'C1=K6/t':K**6/t,'B0=U/2+K/3':U/2+K/3,'B1=zUK/2':z*U*K/2}
funs={'p':S.Matrix([1,0]),'p_H':MH[:,0],'p_B':MB[:,0],
      'F0':S.Matrix([27*B**2*C*H/(5*D**2),-3*C*(8*B**3-27*C*H**2)/(10*D**2)])}

def encode(expr,variables):
 num,den=S.fraction(S.cancel(expr))
 def terms(pol):return[(tuple(ex),int(co.p),int(co.q))for ex,co in S.Poly(pol,*variables).terms()]
 return terms(num),terms(den)

def evaluate(encoded,values,p):
 def poly(terms):
  out=np.zeros(values.shape[1],dtype=np.int64)
  for ex,num,den in terms:
   term=np.full(values.shape[1],num*pow(den,-1,p)%p,dtype=np.int64)
   for i,k in enumerate(ex):
    for _ in range(k):term=term*values[i]%p
   out=(out+term)%p
  return out
 n,d=map(poly,encoded)
 if np.any(d==0):raise ZeroDivisionError
 return n*np.array([pow(int(a),-1,p)for a in d],dtype=np.int64)%p

def prepared():
 fields=[[encode(h,qs)]+[encode(S.diff(h,q),qs)for q in qs]for h in phys]
 base={name:[encode(h,qs)]+[encode(S.diff(h,q),qs)for q in qs]for name,h in hs.items()}
 grads={}
 for name,F in funs.items():
  grads[name]=[[encode(a,[H,B,C])for a in F.diff(v)+M*F]for v,M in zip([H,B,C],[MH,MB,MC])]
 return fields,base,grads

def inputs(points,p,prep):
 fields,base,grad=prep;values=points.T;n=len(points)
 data=np.array([[evaluate(expr,values,p)for expr in row]for row in fields])
 hv,bv,cv=data[:,0];dval=(4*bv*bv%p*bv+27*cv*hv%p*hv)%p
 if np.any(hv==0)or np.any(cv==0)or np.any(dval==0):raise ZeroDivisionError
 iv=lambda a:np.array([pow(int(z),-1,p)for z in a],dtype=np.int64)
 i3=pow(3,-1,p);i9=pow(9,-1,p);ci=iv(cv)
 def mul(a,b):
  a0,a1,a2=a;b0,b1,b2=b
  cross=(a1*b2+a2*b1)%p
  c0=(a0*b0-2*bv*ci%p*i3%p*a1%p*b1-hv*ci%p*cross+2*bv*bv%p*ci%p*ci%p*i9%p*a2%p*b2)%p
  c1=(a0*b1+a1*b0-bv*ci%p*i3%p*cross-hv*ci%p*a2%p*b2)%p
  c2=(a0*b2+a2*b0+a1*b1+bv*ci%p*i3%p*a2%p*b2)%p
  return np.array([c0,c1,c2])
 differentials={}
 for name,gr in grad.items():
  univ=np.array([[evaluate(e,np.array([hv,bv,cv]),p)for e in row]for row in gr])
  out=np.zeros((4,3,n),dtype=np.int64)
  for i in range(4):
   for j in range(3):out[i,1:]=(out[i,1:]+univ[j]*data[j,i+1])%p
  differentials['d('+name+')']=out
 for name,row in base.items():
  evaluated=np.array([evaluate(e,values,p)for e in row]);h=evaluated[0]
  if np.any(h==0):raise ZeroDivisionError
  out=np.zeros((4,3,n),dtype=np.int64);out[:,0]=evaluated[1:]
  differentials['d('+name+')']=out
  differentials['dlog('+name+')']=out*iv(h)%p
 # Rational logarithmic differentials in the cubic field are closed too.
 zero=np.zeros(n,dtype=np.int64);one=np.ones(n,dtype=np.int64)
 invp=np.array([-bv*iv(hv)%p*i3%p,zero,-cv*iv(hv)%p])
 invg=np.array([zero,-9*cv*hv%p*iv(dval)%p,6*bv*cv%p*iv(dval)%p])
 pp=np.array([zero,one,zero]);dp=differentials['d(p)']
 dlogp=np.array([mul(dp[i],invp)for i in range(4)])
 dg=[]
 for i in range(4):
  v0=(data[1,i+1]-2*bv*ci%p*data[2,i+1])%p
  baseg=np.array([v0,zero,3*data[2,i+1]%p])
  dg.append((baseg+6*cv*mul(pp,dp[i]))%p)
 differentials['dlog(p)']=dlogp
 differentials['dlog(g)']=np.array([mul(a,invg)for a in dg])
 def bracket(a,b):
  return(3*values[0]*values[0]%p*(mul(a[0],b[1])-mul(a[1],b[0]))+6*values[3]*(mul(a[2],b[3])-mul(a[3],b[2])))%p
 # Canonical forms: at least one differential must involve the cubic field.
 fieldnames=['d('+name+')'for name in funs]+['dlog(p)','dlog(g)']
 pairs=[]
 for fn in fieldnames:
  for hn in hs:
   for mode in ['d','dlog']:pairs.append((fn,mode+'('+hn+')'))
 pairs+=list(itertools.combinations(fieldnames,2))
 mat=np.column_stack([bracket(differentials[a],differentials[b])[1:].T.reshape(-1)for a,b in pairs])
 source=np.array([bv*(27*cv*hv%p*hv-2*bv*bv%p*bv)%p,-27*bv*bv%p*cv%p*hv%p])*iv(dval)%p*iv(dval)%p
 return mat,source.T.reshape(-1),pairs

def sample(n,p,seed,prep):
 rng=np.random.default_rng(seed);out=[]
 while len(out)<n:
  pt=rng.integers(1,p,size=(1,4),dtype=np.int64)
  try:inputs(pt,p,prep)
  except ZeroDivisionError:continue
  out.append(pt[0])
 return np.array(out,dtype=np.int64)

def run(p=1009):
 prep=prepared();n=6*len(hs)*2+15;count=n+12
 print({'closed_two_forms':n,'generic_points':count,'prime':p},flush=True)
 points=sample(count,p,810294,prep);mat,rhs,pairs=inputs(points,p,prep)
 rank,sol=solve_mod(mat,rhs,p,progress=True)
 report={'prime':p,'closed_two_forms':len(pairs),'rank':rank,'points':count,
         'consistent':sol is not None,'source':'B*p/g^3 times actual Omega',
         'columns':'tracefree projection of displayed closed rational 2forms'}
 if sol is None:report['status']='no candidate in this finite constant-coefficient closed-form closure'
 else:
  fresh=sample(500,p,902182,prep);fm,fr,_=inputs(fresh,p,prep);res=(fm@sol-fr)%p
  report['fresh_nonzero_residuals']=int(np.count_nonzero(res))
  report['candidate']=[{'wedge':pair,'coefficient':int(c)}for pair,c in zip(pairs,sol)if c]
  report['status']='modular candidate requires exact rational lifting'if not np.any(res)else'fresh points reject candidate'
 (root/'closed-form-closure-results.json').write_text(json.dumps(report,indent=2))
 print(json.dumps({k:v for k,v in report.items()if k!='candidate'},indent=2),flush=True)
if __name__=='__main__':run()
