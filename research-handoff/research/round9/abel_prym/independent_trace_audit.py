"""Independent dual-number replay of the 11 Gamma-traced current fields.

Native coordinate derivatives are obtained symbolically, then evaluated
recursively in one-variable dual numbers. This does not use the search
module's second-jet class, polynomial compiler, or trace evaluator.
"""
from pathlib import Path
import json,pickle,sympy as S,time
from functools import lru_cache

HERE=Path(__file__).parent;start=time.monotonic()
hold=json.load(open('/workspace/research/round9/coupled_search/marked_fields_holdouts.json'))
prime=hold['prime']
class D:
 def __init__(self,a=0,b=0):
  if isinstance(a,D):self.a,self.b=a.a,a.b
  else:self.a,self.b=int(a)%prime,int(b)%prime
 def __add__(a,b):
  b=D(b);return D(a.a+b.a,a.b+b.b)
 __radd__=__add__
 def __neg__(a):return D(-a.a,-a.b)
 def __sub__(a,b):return a+-D(b)
 def __rsub__(a,b):return D(b)+-a
 def __mul__(a,b):
  b=D(b);return D(a.a*b.a,a.a*b.b+a.b*b.a)
 __rmul__=__mul__
 def __pow__(a,n):
  if not n:return D(1)
  return D(pow(a.a,n,prime),n*pow(a.a,n-1,prime)*a.b)
 def __truediv__(a,b):return a*D(b)**-1
 def __rtruediv__(a,b):return D(b)*a**-1

class Q:
 P=None;c=None
 def __init__(self,a=0,b=0):self.a,self.b=D(a),D(b)
 def __add__(a,b):
  if not isinstance(b,Q):b=Q(b)
  return Q(a.a+b.a,a.b+b.b)
 __radd__=__add__
 def __neg__(a):return Q(-a.a,-a.b)
 def __sub__(a,b):return a+-b if isinstance(b,Q) else a+-Q(b)
 def __rsub__(a,b):return Q(b)+-a
 def __mul__(a,b):
  if not isinstance(b,Q):b=Q(b)
  return Q(a.a*b.a-Q.P*a.b*b.b,a.a*b.b+a.b*b.a-Q.c*a.b*b.b)
 __rmul__=__mul__
 def __pow__(a,n):
  if n<0:
   den=a.a*a.a-Q.c*a.a*a.b+Q.P*a.b*a.b
   return Q((a.a-Q.c*a.b)/den,-a.b/den)**(-n)
  out=Q(1)
  while n:
   if n%2:out=out*a
   n//=2;a=a*a
  return out
 def __truediv__(a,b):return a*(b if isinstance(b,Q) else Q(b))**-1
 def __rtruediv__(a,b):return Q(b)*a**-1

a,b,v=S.symbols('a b v');c=S.Rational(5,7)
B=b*(1+a*v);P=1+v**6;Cq=c*a*b*v;R=c*(a*b+v*b**3);SS=1+a**6+b**6
A=3*SS-B*R;M=A/(3*SS);zz=B*R/A
pars=[(27*P*SS**2-9*Cq*R*SS+2*R**3)/(3*A*A),(3*SS*Cq-R*R)/(B*A),3*B**3/A]
derivs=[[S.diff(e,s)for e in pars]for s in(a,b)]
logrho=[(S.diff(A,s)/A-S.diff(SS,s)/SS)/3 for s in(a,b)]
fT=3*a**3*SS/(2*B**3*A)
blocks=[]
for name,ids,ch in [('actual',[0,1],1),('conjugate',[0],2)]:
 data=pickle.load(open('/workspace/research/round9/cyclic_full/'+name+'_fast.pickle','rb'))
 for idx in ids:blocks.append((name,idx,ch,data))

def evaluator(values):
 @lru_cache(None)
 def ev(e):
  if e.is_Rational:return D(int(e.p))/int(e.q)
  if e.is_Symbol:return values[e]
  if e.is_Add:return sum((ev(x)for x in e.args),D(0))
  if e.is_Mul:
   z=D(1)
   for x in e.args:z*=ev(x)
   return z
  if e.is_Pow:return ev(e.base)**int(e.exp)
  raise TypeError(e)
 return ev

counts={'field_values':0,'field_first_derivatives':0,'density_values':0,'density_first_derivatives':0}
for record in hold['records']:
 point=record['point']
 for direction in (0,1):
  native=evaluator({s:D(x,int(i==direction))for i,(s,x)in enumerate(zip((a,b,v),point))})
  cp=[native(e)for e in pars];z=native(zz);mm=native(M)
  Q.P=native(P);Q.c=native(c);u=Q(0,1)
  ct=Q(native(c))*u/mm+cp[1]+3*z*z/cp[2]
  fields=[]
  for name,idx,ch,data in blocks:
   canonical=evaluator(dict(zip(data['symbols'][3:],cp)))
   Ubar=[]
   for bn in ('L','r','x'):
    pp=data['primitives'][bn][idx];g=Q(0)
    for coeff,(component,ex)in zip(pp['Q8_raw'],data['lab8']):
     if component not in(0,1)or coeff==0:continue
     power=ex[0]+int(component==1)
     assert (power-ch)%3==0
     g+=((-1 if component==1 else 1)*Q(canonical(coeff))*(u/mm)**((power-ch)//3)*z**ex[2])
    Ubar.append(g/canonical(pp['Q8_denominator']))
   RR=[]
   for i in(0,1):
    num=Q(-native(logrho[i])*(z if name=='actual'and idx==1 else 1))
    num+=sum((g*native(de)for g,de in zip(Ubar,derivs[i])),Q(0))
    RR.append(num/ct)
   for j in range(3 if name=='actual' else 4):
    fields.append((f'{name}{idx}_v{j}',RR[1].b*point[2]**j,-RR[0].b*point[2]**j))
   if name=='conjugate':fields.append(('conjugate0_u',RR[1].a-native(c)*RR[1].b,-RR[0].a+native(c)*RR[0].b))
  for (name,xa,xb),expected in zip(fields,record['fields']):
   assert name==expected['name']
   for key,x in [('Xa',xa),('Xb',xb)]:
    assert x.a==expected[key],(point,name,key,x.a,expected[key])
    assert x.b==expected['d'+key+'_ab'][direction],(point,name,key,direction,x.b,expected['d'+key+'_ab'][direction])
    counts['field_values']+=1;counts['field_first_derivatives']+=1
  ft=native(fT);assert ft.a==record['fT']['value'] and ft.b==record['fT']['gradient_ab'][direction]
  counts['density_values']+=1;counts['density_first_derivatives']+=1
out={'prime':prime,'points':[r['point']for r in hold['records']],'checks':counts,
 'all11_fields_and_first_derivatives_match':True,'method':'Independent recursive symbolic evaluation in one-variable dual numbers; native coordinate derivatives computed with SymPy, no imported search jet engine.',
 'trace_identity':'Full Gamma trace is coefficient_u(R); extra conjugate weight is R0-cR1.',
 'seconds':time.monotonic()-start,'scope':'Verifies the traced current evaluator and its retained derivatives. Does not assert a source solution or Gysin support.'}
(HERE/'independent_trace_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
