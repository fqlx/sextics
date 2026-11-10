from pathlib import Path
import json,time,sympy as S
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq
st=time.time();names=['u','b','c','d','z','ell'];us,bs,cs,ds,zs,ls=S.symbols(' '.join(names));env=dict(zip(names,[us,bs,cs,ds,zs,ls]));Ks=S.Symbol('K');env['K']=Ks;K0=2*(1+cs**6);C=fmpq_mpoly_ctx.get(tuple(names));u,b,c,d,z,ell=C.gens();zero=C.constant(0);one=C.constant(1);K=2*(1+c**6);F=b**6+d**6+ell*u**3+K;g=3*ell*u*u
D=json.load(open(Path(__file__).resolve().parent / 'second_source_complete.json'));records=json.load(open(Path(__file__).resolve().parent / 'second_character_classification.json'))['residual'];lookup={(r['b_power'],r['d_power'],r['u_pole']):r for r in records};assert len(D['residual_currents'])==len(lookup)==35 and not D['unresolved']
def cv(p):
 P=S.Poly(p,*[us,bs,cs,ds,zs,ls],domain=S.QQ);return C.from_dict({ex:fmpq(int(v.p),int(v.q)) for ex,v in P.terms()})
def rat(expr):
 expr=S.sympify(expr,locals=env).subs(Ks,K0);n,d=S.fraction(S.cancel(expr));return cv(n),cv(d)
def exact_div(a,b):q,r=divmod(a,b);assert r.is_zero();return q
def lcm(a,b):return exact_div(a,a.gcd(b))*b
out=[]
for item in D['residual_currents']:
 mode=tuple(item['mode']);r,s,k=mode;nums=[];dens=[]
 for expr in item['beta']:
  n,d0=rat(expr);nums.append(n);dens.append(d0)
 common=one
 for ni,di in zip(nums,dens):
  if not ni.is_zero():common=lcm(common,di)
 numt=one if item['type']=='unit' else None
 if item['type']=='unit':tn=b**r*d**s;td=u**k
 else:
  cn,cd=rat(lookup[mode]['coefficient']);tn=cn*b**r*d**s;td=cd*u**k
 total=zero
 for i,(ni,di) in enumerate(zip(nums,dens)):
  if ni.is_zero():continue
  fac=exact_div(common,di);der=g*(ni.derivative(i+1)*di-ni*di.derivative(i+1))-F.derivative(i+1)*(ni.derivative(0)*di-ni*di.derivative(0));total+=der*fac**2
 raw=total*td-g*common**2*tn;quo,rem=divmod(raw,F);assert rem.is_zero() and raw==quo*F,('mode',mode,'type',item['type'],'remainder',len(rem));out.append({'mode':mode,'type':item['type'],'quotient_terms':len(quo)});print('PASS',mode,item['type'],'quotient',len(quo),'elapsed',round(time.time()-st,1),flush=True)
