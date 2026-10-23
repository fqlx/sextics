"""Exact weighted degree5 initial form at all algebraic T0 special points.
Use D=e²-E0 as etale coordinate, rather than choosing a square root e0.
"""
from pathlib import Path
import pickle,json,sympy as s
H=Path(__file__).parent;d=pickle.load(open(H/'strict_normalization.pickle','rb'));a,b,t,v,e=d['variables'];D,z,eta=s.symbols('D z eta');vars=(D,z,b,eta);weights=(1,2,2,1);kv=s.Rational(-171,196)
def reduce(f):
 out={}
 for term in s.Add.make_args(s.expand(f)):
  pw=term.as_powers_dict();ia=int(pw.get(a,0));iv=int(pw.get(v,0));mm=tuple(int(pw.get(x,0))for x in vars)
  if sum(i*w for i,w in zip(mm,weights))>5:continue
  cc=s.cancel(term/(a**ia*v**iv*s.prod(x**j for x,j in zip(vars,mm))))
  assert cc.is_Rational,(term,cc)
  key=(ia%6,iv%6)+mm;sg=(-1 if ia//6%2 else 1)*kv**(iv//6)
  out[key]=out.get(key,0)+cc*sg
 return s.Add(*(cc*a**key[0]*v**key[1]*s.prod(x**i for x,i in zip(vars,key[2:]))for key,cc in out.items()if cc))
def at(f):return reduce(f.subs({b:0,t:1}))
def DS(f):return s.diff(f,a)/(6*a**5)
def DT(f):return s.diff(f,v)/(1176*v**5)
C={}
for n in [13,15]:
 q,r,ss=d['parts'][n]
 ops=dict(qT=DT(q),rT=DT(r),rTT=DT(DT(r)),rS=DS(r),sS=DS(ss),sST=DS(DT(ss)),sbT=s.diff(DT(ss),b),sbb=s.diff(ss,b,2)/2,sbS=s.diff(DS(ss),b))
 C[n]={k:at(f)for k,f in ops.items()}
h=a*v;k=9*h-5;E0=-k/(28*a);E=E0+D;S=b*eta
# Actual implicit F, solved to weighted order4.  Remainder starts in weight5.
base=-196*z*z-10*k*b*E-140*a*b*E**2-140*b*E*z*(1+h)-196*E**3*S
T=reduce(base+s.Rational(5,57)*h*b*b*E0*(-10*k*E0-140*a*E0**2))
# remove weight5 terms in T (they cannot contribute to the weight5 model)
T=s.Add(*(term for term in s.Add.make_args(s.expand(T))if sum(int(term.as_powers_dict().get(x,0))*w for x,w in zip(vars,weights))<=4))
cc={j:reduce(C[13][j]+E*C[15][j])for j in C[13]}
f=cc['qT']*T*eta**2+(cc['rT']*T+cc['rTT']*T*T/2+cc['rS']*S)*eta+cc['sS']*S+cc['sST']*T*S+cc['sbT']*T*b+cc['sbb']*b*b+cc['sbS']*b*S
f=reduce(f)
rows={}
for term in s.Add.make_args(s.expand(f)):
 pw=term.as_powers_dict();mm=tuple(int(pw.get(x,0))for x in vars);cc0=s.cancel(term/s.prod(x**i for x,i in zip(vars,mm)))
 rows[mm]=rows.get(mm,0)+cc0
rows={mm:s.factor(cc0)for mm,cc0 in rows.items()if cc0}
low={mm:cc0 for mm,cc0 in rows.items()if sum(i*w for i,w in zip(mm,weights))<5};assert not low,low
result=dict(variables=[str(x)for x in vars],weights=weights,degree=5,relations=['a6=-1','196v6+171=0'],criticalE='e²=-(9av-5)/(28a)',terms={','.join(map(str,mm)):str(cc0)for mm,cc0 in rows.items()},lowerTermsVanishExactly=True,scope='Exact all-orbit weighted initial form. Normality/resolution and global source map are separate.')
pickle.dump(dict(variables=(a,v,D,z,b,eta),coefficients=C,T=T,initial=f,terms=rows,E0=E0),open(H/'T0_weighted_symbolic.pickle','wb'));(H/'T0_weighted_symbolic.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
