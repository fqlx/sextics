#!/usr/bin/env python3
"""Finite exact logarithmic w-cokernel presentation for the actual Euler source.
This is a presentation, not a claimed primitive or a completed horizontal solve.
"""
import json,time,hashlib
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
from construct_source_taylor_current import L,C as C2,I,J,ONE,ZERO
W=fmpq_mpoly_ctx.get(('i','j','w'));i,j,w=W.gens();V=fmpq_mpoly_ctx.get(('i','j','v'));zero=W.constant(0)
class LP:
 def __init__(self,p=0,si=0,sj=0):
  self.p=p if isinstance(p,fmpq_mpoly) else W.constant(p);self.si=int(si);self.sj=int(sj)
  if not self.p:self.si=self.sj=0
  else:
   a,b,k=next(iter(self.p.term_content().to_dict()));mon=i**a*j**b
   self.p=self.p//mon;self.si+=int(a);self.sj+=int(b)
 def __add__(self,z):
  z=lp(z)
  if not self.p:return z
  if not z.p:return self
  a=min(self.si,z.si);b=min(self.sj,z.sj)
  return LP(self.p*i**(self.si-a)*j**(self.sj-b)+z.p*i**(z.si-a)*j**(z.sj-b),a,b)
 __radd__=__add__
 def __neg__(self):return LP(-self.p,self.si,self.sj)
 def __sub__(self,z):return self+-lp(z)
 def __mul__(self,z):
  z=lp(z);return LP(self.p*z.p,self.si+z.si,self.sj+z.sj)
 __rmul__=__mul__
 def divpoly(self,z):
  quo,rem=divmod(self.p,z);assert not rem
  return LP(quo,self.si,self.sj)
 def dump(self):return {'polynomial':str(self.p),'parameter_shift':[self.si,self.sj]}

def lp(x):
 if isinstance(x,LP):return x
 if isinstance(x,L):return LP(W.from_dict({(a,b,0):z for (a,b),z in x.p.to_dict().items()}),x.si,x.sj)
 return LP(x)

def main():
 t=time.monotonic();path=Path(__file__).with_name('rank8-descended-connection-results.json');raw=path.read_bytes();g=json.loads(raw)
 ep=path.parent.parent/'ruling-source/full-base-connection/source-euler-current-results.json';eraw=ep.read_bytes();es=json.loads(eraw)
 N=9*i*i*w*w-16*j*j*(1+w**3);T=1+w**3;LL=256*T**5*N+729*i**6*j*j*w**6
 A=64*j*j*w*N*T*T;B=9*i*i*LL;Ccrit,rem=divmod(A.derivative(2)*B-A*B.derivative(2),T);assert not rem
 Ap=[W.constant(1)];Bp=[W.constant(1)]
 for k in range(1,6):Ap.append(Ap[-1]*A);Bp.append(Bp[-1]*B)
 def compose(txt,deg):
  pp=fmpq_mpoly(txt,V);return sum((W.from_dict({(a,b,0):z})*Ap[k]*Bp[deg-k] for (a,b,k),z in pp.to_dict().items()),zero)
 Dc=compose(g['GammaV_denominator'],4)
 EDen=compose(es['remaining_common_denominator'],4)
 # D and remaining-source denominators may differ by a nonzero rational factor.
 ratq,rr=divmod(EDen,Dc);assert not rr and ratq.degrees()==(0,0,0)
 rat=ratq.to_dict().get((0,0,0),fmpq(0));assert rat
 D0=fmpq_mpoly(g['GammaV_denominator'],V).to_dict().get((0,0,0));assert D0
 def v0(txt):return L(C2.from_dict({(a,b):z for (a,b,k),z in fmpq_mpoly(txt,V).to_dict().items() if k==0}))
 R0=[[v0(txt)/(6*D0) for txt in ar] for ar in g['GammaV_numerator']]
 q0=[v0(txt)/D0/rat for txt in es['remaining_vector_numerators']]
 sinf1=[z*(-fmpq(9,16)*I*I*I/(J*J*J*J)) for z in q0]
 sinf0=[z*(fmpq(9,16)*I*I/(J*J)) for z in sinf1]
 order=[0,4,1,5,2,6,3,7]
 def solve_infinity(n,rhs):
  out=[ZERO]*8
  for pp,a in enumerate(order):out[a]=(rhs[a]+sum((8*R0[a][b]*out[b] for b in order[:pp]),ZERO))/(n-8*R0[a][a])
  return out
 p2=solve_infinity(2,sinf1);p1=solve_infinity(1,sinf0)
 source=[];s=[1,1,0,0,1,1,0,0];K=[[] for _ in range(8)];Hp=[];domainchecks=[]
 for rrrow in range(8):
  H=w*N*T*Dc*LL**(1+s[rrrow]);Hp.append(H)
  Sc=LP(9*i**3*w*w*T*T*LL**(1+s[rrrow])*compose(es['remaining_vector_numerators'][rrrow],4),0,-2)*LP(1/rat)
  GP=LP();
  for cc in range(8):
   gc=compose(g['GammaV_numerator'][rrrow][cc],5)
   kk=LP(Ccrit*gc,fmpq(0),fmpq(0))*LP(fmpq(1,31104),-4,-2)
   if not s[rrrow]:kk=kk.divpoly(LL)
   K[rrrow].append(kk)
   if s[cc]:
    quotient=kk.divpoly(LL);domainchecks.append(quotient.p.degrees()[2]+18<=H.degrees()[2]-1)
   GP=GP+kk*(lp(p2[cc])*w*w+lp(p1[cc])*w)
  final=Sc-GP-LP(H)*(2*w*lp(p2[rrrow])+lp(p1[rrrow]))
  assert final.p.degrees()[2]<=H.degrees()[2]-1,(rrrow,final.p.degrees()[2],H.degrees()[2])
  source.append(final.dump());print('source row',rrrow,'terms',len(final.p.to_dict()),'seconds',round(time.monotonic()-t,2),flush=True)
 assert all(domainchecks)
 result={
  'status':'Exact finite logarithmic w-cokernel presentation and actual source class; horizontal primitive remains open',
  'certificate':False,'matrix_orientation':'columns are zero-form currents, rows are logarithmic one-form coefficients',
  'coefficient_field':'Q(i,j)','curve_basis':g['compact_basis'],'source_volume':'di dj dw',
  'N':str(N),'T':str(T),'L':str(LL),'v_numerator_A':str(A),'v_denominator_B':str(B),
  'discriminant_pullback_Dc':str(Dc),'row_shear':s,
  'row_denominator_formula':'H_r=w*N*T*Dc*L^(1+s_r)',
  'row_degrees':[int(h.degrees()[2]) for h in Hp],
  'row_coefficients':'for eachr use [w^0,...,w^(degH_r-1)] of numerator in Q(i,j)',
  'zero_form_columns':'for each s_c=1, P=e_c*w^k/L, k=0,...,18; for each s_c=0, P=e_c',
  'zero_form_dimension':80,'one_form_dimension':sum(int(h.degrees()[2]) for h in Hp),
  'K_formula':'K_rc=H_r*Gamma_w[r,c]=(Ccrit*compose5(GammaVnum_rc))/(31104*i^4*j^2*L^(1-s_r)); Ccrit=(A_w*B-A*B_w)/T',
  'matrix_constant_column':'column e_c has numerator K_rc',
  'matrix_fraction_column':'column e_c*w^k/L has numerator (K_rc/L)*w^k + delta_rc*w*N*T*Dc*(k*w^(k-1)*L-w^k*L_w)',
  'known_infinity_current_p2':[x.dump() for x in p2],'known_infinity_current_p1':[x.dump() for x in p1],
  'known_infinity_current':'Pinf=w²*p2+w*p1; subtract its literal full connection current, including audited fiber primitives',
  'actual_source_numerators':source,
  'actual_source_convention':'R_r=parameter_shift_monomial*actual_source_numerators[r].polynomial/H_r',
  'source_connection_sha256':hashlib.sha256(raw).hexdigest(),'euler_source_sha256':hashlib.sha256(eraw).hexdigest(),
  'checks':{'all_source_rows_logarithmic_at_infinity':True,'all_80_columns_preserve_logarithmic_pole_space':True,'source_remaining_denominator_constant_ratio':str(rat),'infinity_connection_wminus2_term_zero':True},
  'horizontal_action':'on quotient apply partial_i+Gamma_i+(v_i/(6v))*GammaV, and similarlyj, then remove higher poles with the exact local residue inverses; flatness makes image of w-connection stable',
  'seconds':round(time.monotonic()-t,3),
 }
 out=path.with_name('source-leray-presentation-results.json');out.write_text(json.dumps(result,indent=2)+'\n');print('saved',out,'dimension',result['one_form_dimension'],'seconds',round(time.monotonic()-t,2),flush=True)
if __name__=='__main__':main()
