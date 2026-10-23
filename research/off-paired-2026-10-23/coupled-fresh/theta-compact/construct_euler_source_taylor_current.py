#!/usr/bin/env python3
"""Complete source-bound rational reconstruction from local exponent bounds.
Native Laurent polynomial arithmetic in i,j, never coefficient specialization.
"""
import json,time,sys
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
C=fmpq_mpoly_ctx.get(('i','j'));ii,jj=C.gens()
class L:
 __slots__=('p','si','sj')
 def __init__(self,p=0,si=0,sj=0,norm=True):
  self.p=p if isinstance(p,fmpq_mpoly) else C.constant(p);self.si=si;self.sj=sj
  if not self.p:self.si=self.sj=0
  elif norm:
   tc=self.p.term_content();key=next(iter(tc.to_dict()));a,b=key
   if a or b:self.p=self.p//tc;self.si+=a;self.sj+=b
 def __bool__(self):return bool(self.p)
 def __add__(self,b):
  b=asL(b)
  if not self:return b
  if not b:return self
  si=min(self.si,b.si);sj=min(self.sj,b.sj)
  return L(self.p*ii**(self.si-si)*jj**(self.sj-sj)+b.p*ii**(b.si-si)*jj**(b.sj-sj),si,sj)
 __radd__=__add__
 def __neg__(self):return L(-self.p,self.si,self.sj,False)
 def __sub__(self,b):return self+-asL(b)
 def __rsub__(self,b):return asL(b)+-self
 def __mul__(self,b):
  b=asL(b)
  if not self or not b:return ZERO
  return L(self.p*b.p,self.si+b.si,self.sj+b.sj,False)
 __rmul__=__mul__
 def inv(self):
  dd=self.p.to_dict();assert len(dd)==1 and (0,0) in dd,('nonunit',self.dump())
  return L(C.constant(1/dd[(0,0)]),-self.si,-self.sj,False)
 def __truediv__(self,b):return self*asL(b).inv()
 def euler(self):return L(2*ii*self.p.derivative(0)+jj*self.p.derivative(1)+(2*self.si+self.sj)*self.p,self.si,self.sj)
 def dump(self):return {'poly':str(self.p),'shift':[int(self.si),int(self.sj)]}
 def __repr__(self):return str(self.dump())
def asL(x):return x if isinstance(x,L) else L(x)
ZERO=L();ONE=L(1);I=L(ii);J=L(jj)
NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 24

def pad(a):return (a+[ZERO]*NMAX)[:NMAX]
def add(a,b):return [x+y for x,y in zip(pad(a),pad(b))]
def scale(a,b):return [x*b for x in a]
def mul(a,b):
 out=[ZERO]*NMAX
 for k,x in enumerate(a[:NMAX]):
  if not x:continue
  for l,y in enumerate(b[:NMAX-k]):
   if y:out[k+l]=out[k+l]+x*y
 return out

def inv(a):
 ai=a[0].inv();out=[ai]
 for n in range(1,NMAX):out.append(-ai*sum((a[k]*out[n-k] for k in range(1,min(n+1,len(a)))),ZERO))
 return out

def div(a,b):return mul(a,inv(b))
def power(a,n):
 out=pad([ONE])
 for k in range(n):out=mul(out,a)
 return out

def shift(a,n=1):return pad([ZERO]*n+a)
def der(a):return pad([a[n]*n for n in range(1,len(a))])
def eul(a):return [x.euler() for x in a]
def const(a):return pad([asL(a)])
def from_poly(poly,ctx):
 out=[ZERO]*NMAX
 for (a,b,k),coef in poly.to_dict().items():
  if k<NMAX:out[k]=out[k]+L(C.from_dict({(a,b):coef}))
 return out

def main():
 t=time.monotonic();path=Path(__file__).with_name('rank8-descended-connection-results.json');data=json.loads(path.read_text());CV=fmpq_mpoly_ctx.get(('i','j','v'))
 # v(w) uses N=9i²w²−16j²(1+w³), L=256T^5N+729i^6j²w^6.
 T=pad([ONE,ZERO,ZERO,ONE]);N=pad([-16*J*J,ZERO,9*I*I,-16*J*J]);LL=add(scale(mul(power(T,5),N),256),shift(const(729*powerL(I,6)*J*J),6))
 vn=scale(shift(mul(N,power(T,2))),64*J*J);vd=scale(LL,9*I*I);vs=div(vn,vd)
 # Need v/w through orderNMAX-1; recompute one additional coefficient exactly.
 # For present source reconstruction the highest derivative coefficient is not
 # needed because Q0=Q1=0; padding v/w's final coefficient is harmless there.
 tv=pad(vs[1:]);wlog=add(const(ONE),div(shift(der(tv)),tv))
 Woverv=add(const(6),div(eul(tv),tv))
 a0=div(scale(shift(T),54*powerL(I,3)/(J*J)),N)
 r=add(a0,scale(eul(a0),-1))
 # Evaluate all generic v-polynomials from shared powers v^k.
 vp=[const(ONE)]
 for k in range(1,6):vp.append(mul(vp[-1],vs))
 def evaluate(txt):
  pp=fmpq_mpoly(txt,CV);out=[ZERO]*NMAX
  for (a,b,k),coef in pp.to_dict().items():out=add(out,scale(vp[k],L(C.from_dict({(a,b):coef}))))
  return out
 ds=evaluate(data['GammaV_denominator']);dinv=inv(ds)
 Gam=[[mul(evaluate(txt),dinv) for txt in ar] for ar in data['GammaV_numerator']]
 B=[[scale(mul(wlog,z),fmpq(1,6)) for z in ar] for ar in Gam]
 euler_path=path.parent.parent/'ruling-source'/'full-base-connection'/'source-euler-current-results.json'
 edata=json.loads(euler_path.read_text());einv=inv(evaluate(edata['remaining_common_denominator']))
 S=[scale(mul(a0,mul(evaluate(txt),einv)),fmpq(1,6)) for txt in edata['remaining_vector_numerators']]
 print('exact connection/source Taylor coefficients built',round(time.monotonic()-t,2),flush=True)
 # (n I+R0) is lower triangular in this order, with rational nonzero diagonal.
 order=[0,4,1,5,2,6,3,7]
 R0=[[B[a][b][0] for b in range(8)] for a in range(8)]
 assert all(not R0[order[a]][order[b]] for a in range(8) for b in range(a+1,8))
 Q=[[ZERO]*NMAX for _ in range(8)]
 for n in range(NMAX):
  rhs=[(S[a][n-1] if n else ZERO)-sum((B[a][b][k]*Q[b][n-k] for b in range(8) for k in range(1,n+1)),ZERO) for a in range(8)]
  for p,a in enumerate(order):Q[a][n]=(rhs[a]-sum((R0[a][b]*Q[b][n] for b in order[:p]),ZERO))/(n+R0[a][a])
  print('current Taylor order',n,round(time.monotonic()-t,2),flush=True)
 # Denominators are COMPLETE local bounds, not degree guesses.
 shears=[1,1,0,0,1,1,0,0];nums=[];failure=[]
 for a in range(8):
  den=LL if shears[a] else const(ONE)
  nn=mul(Q[a],den);bound=20 if shears[a] else 2
  bad=[k for k in range(bound+1,NMAX) if nn[k]]
  if bad:failure.append({'row':a,'first_excess_order':bad[0],'coefficient':nn[bad[0]].dump()})
  nums.append([x.dump() for x in nn[:bound+1]])
 out=path.with_name('euler-source-taylor-current-results.json')
 result={'status':'Source-bound complete-pole reconstruction; identity verification pending' if not failure else 'Complete w-only rational-pole reconstruction has an exact excess coefficient; full-base currents remain required','certificate':False,'NMAX':NMAX,'basis':data['compact_basis'],'known_horizontal_current':'Full-base Euler current in source-euler-current-results.json','residual_source':'a0/6*(4eb-GammaD eb)','denominator_bound':'L0 for rows0,1,4,5; 1 for rows2,3,6,7','numerator_degree_bound':[20 if z else 2 for z in shears],'failures':failure,'candidate_numerator_coefficients':nums,'seconds':round(time.monotonic()-t,3)}
 out.write_text(json.dumps(result,indent=2)+'\n');print('saved',out,'excess rows',len(failure),flush=True)
def powerL(x,n):
 out=ONE
 for k in range(n):out=out*x
 return out
if __name__=='__main__':main()
